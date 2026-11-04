/* SPDX-License-Identifier: GPL-2.0-only */

#include <linux/errno.h>
#include <linux/jump_label.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/mutex.h>
#include <linux/set_memory.h>
#include <linux/version.h>

#include "compat/jailbreak.h"
#include "infra/symbol_resolver.h"
#include "klog.h"

DEFINE_STATIC_KEY_FALSE(ksu_rkp_key);

void rkp_jb_init(void)
{
    if (find_kernel_symbol_exact("rkp_started")) {
        static_branch_enable(&ksu_rkp_key);
        pr_info("KSU: Samsung RKP detected\n");
    }
}

#ifdef __aarch64__

#include <linux/moduleloader.h>
#include <linux/vmalloc.h>

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 10, 0)
#include <linux/execmem.h>
#define ksu_exec_alloc(sz) execmem_alloc(EXECMEM_MODULE_TEXT, (sz))
#define ksu_exec_free(p) execmem_free(p)
#else
#define ksu_exec_alloc(sz) module_alloc(sz)
#define ksu_exec_free(p) vfree(p)
#endif

#include "hook/patch_memory.h"

#define KSU_MAX_BRANCH_SITES 16
#define KSU_STUB_SIZE 16

#define KSU_PATCH_FLAGS \
    (KSU_PATCH_TEXT_FLUSH_DCACHE | KSU_PATCH_TEXT_FLUSH_ICACHE)

struct ksu_branch_site {
    void *fn_addr;
    u32 insn_at_patch;
    u32 insn_at_fn0;
    int stub_idx;
    int preamble_skip;
};

static struct ksu_branch_site ksu_sites[KSU_MAX_BRANCH_SITES];
static int ksu_site_count;

static DEFINE_MUTEX(ksu_site_lock);

static void *ksu_stub_page;
static int ksu_stub_next;

static u32 ksu_encode_b(void *from, void *to)
{
    s64 imm26;

    if (((unsigned long)from | (unsigned long)to) & 3)
        return 0;

    imm26 = ((s64)(unsigned long)to -
             (s64)(unsigned long)from) >> 2;

    if (imm26 < -(1LL << 25) || imm26 > (1LL << 25) - 1)
        return 0;

    return 0x14000000U | (u32)(imm26 & 0x03FFFFFFU);
}

static bool ksu_insn_is_pac_signing(u32 insn)
{
    return insn == 0xD503233F || insn == 0xD503237F;
}

static bool ksu_insn_is_bti_landing_pad(u32 insn)
{
    return (insn & 0xFFFFFF3F) == 0xD503241F ||
           ksu_insn_is_pac_signing(insn);
}

static bool ksu_insn_is_pc_relative(u32 insn)
{
    return ((insn & 0x1F000000U) == 0x10000000U) ||
           ((insn & 0x3B000000U) == 0x18000000U) ||
           ((insn & 0x7C000000U) == 0x14000000U) ||
           ((insn & 0xFE000000U) == 0x54000000U) ||
           ((insn & 0x7E000000U) == 0x34000000U) ||
           ((insn & 0x7E000000U) == 0x36000000U);
}

static struct ksu_branch_site *ksu_find_site(void *fn)
{
    int i;

    for (i = 0; i < ksu_site_count; i++) {
        if (ksu_sites[i].fn_addr == fn)
            return &ksu_sites[i];
    }

    return NULL;
}

/*
 * Patch one or two instruction locations through the KSU-Next
 * fixmap/stop_machine implementation.
 */
static int ksu_rkp_patch_words(
    void **addresses,
    u32 *instructions,
    size_t count)
{
    struct ksu_patch_entry entries[2];
    size_t i;

    if (!addresses || !instructions || !count || count > 2)
        return -EINVAL;

    for (i = 0; i < count; i++) {
        entries[i].dst = addresses[i];
        entries[i].src = &instructions[i];
        entries[i].len = sizeof(u32);
        entries[i].flags = KSU_PATCH_FLAGS;
    }

    return ksu_patch_text_batch(entries, count);
}

/*
 * Write the complete stub before making it reachable from a live
 * kernel function.
 */
static int ksu_rkp_write_stub(void *stub, const u32 instructions[4])
{
    struct ksu_patch_entry entry = {
        .dst = stub,
        .src = instructions,
        .len = KSU_STUB_SIZE,
        .flags = KSU_PATCH_FLAGS,
    };

    return ksu_patch_text_batch(&entry, 1);
}

int ksu_rkp_branch_patch(void *dst, void *src)
{
    void *current_fn;
    void *new_fn;
    void *stub;
    void *patch_addr;
    void *stub_resume;
    void *restore_addresses[2];
    void *patch_addresses[2];

    struct ksu_branch_site *site;

    u32 insn_at_patch;
    u32 branch_b;
    u32 fn0_insn;
    u32 insn_at_fn0 = 0;
    u32 stub_instructions[4];

    int preamble_skip = 0;
    int stub_idx;
    int ret;

    if (!dst || !src)
        return -EINVAL;

    current_fn = READ_ONCE(*(void **)dst);
    new_fn = READ_ONCE(*(void **)src);

    if (!current_fn || !new_fn)
        return -EINVAL;

    mutex_lock(&ksu_site_lock);

    /*
     * If this function was already patched, restore its original
     * instructions before installing the replacement.
     */
    site = ksu_find_site(current_fn);

    if (site) {
        restore_addresses[0] =
            (u8 *)current_fn + site->preamble_skip * sizeof(u32);

        restore_addresses[1] = current_fn;

        {
            u32 restore_instructions[2];

            restore_instructions[0] = site->insn_at_patch;
            restore_instructions[1] = site->insn_at_fn0;

            ret = ksu_rkp_patch_words(
                restore_addresses,
                restore_instructions,
                site->insn_at_fn0 ? 2 : 1);

            if (ret) {
                mutex_unlock(&ksu_site_lock);
                pr_err("KSU: RKP restore failed at %pS: %d\n",
                       current_fn, ret);
                return ret;
            }
        }

        *site = ksu_sites[--ksu_site_count];

        pr_info("KSU: RKP branch site removed at %pS\n",
                current_fn);

        if (new_fn == current_fn) {
            mutex_unlock(&ksu_site_lock);
            return 0;
        }
    }

    if (current_fn == new_fn) {
        mutex_unlock(&ksu_site_lock);
        return 0;
    }

    if (ksu_site_count >= KSU_MAX_BRANCH_SITES) {
        mutex_unlock(&ksu_site_lock);
        pr_err("KSU: RKP branch site table full\n");
        return -ENOMEM;
    }

    if (!ksu_stub_page) {
        ksu_stub_page = ksu_exec_alloc(PAGE_SIZE);

        if (!ksu_stub_page) {
            mutex_unlock(&ksu_site_lock);
            return -ENOMEM;
        }

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 3, 0)
        ret = set_memory_rox((unsigned long)ksu_stub_page, 1);
#else
        ret = set_memory_ro((unsigned long)ksu_stub_page, 1);
        if (!ret)
            ret = set_memory_x((unsigned long)ksu_stub_page, 1);
#endif

        if (ret) {
            ksu_exec_free(ksu_stub_page);
            ksu_stub_page = NULL;
            mutex_unlock(&ksu_site_lock);

            pr_err("KSU: RKP stub page permission setup failed: %d\n",
                   ret);
            return ret;
        }
    }

    if (ksu_stub_next >= PAGE_SIZE / KSU_STUB_SIZE) {
        mutex_unlock(&ksu_site_lock);
        pr_err("KSU: RKP stub page full\n");
        return -ENOMEM;
    }

    fn0_insn = READ_ONCE(*(u32 *)current_fn);
    insn_at_patch = fn0_insn;

    /*
     * Preserve BTI/PAC preamble instructions at function entry.
     */
    while (preamble_skip < 2 &&
           ksu_insn_is_bti_landing_pad(insn_at_patch)) {
        preamble_skip++;

        insn_at_patch = READ_ONCE(
            *(u32 *)((u8 *)current_fn +
                     preamble_skip * sizeof(u32)));
    }

    patch_addr = (u8 *)current_fn +
                 preamble_skip * sizeof(u32);

    stub_resume = (u8 *)current_fn +
                  (preamble_skip + 1) * sizeof(u32);

    if (ksu_insn_is_pc_relative(insn_at_patch)) {
        mutex_unlock(&ksu_site_lock);

        pr_err("KSU: %pS: PC-relative instruction at offset %d\n",
               current_fn, preamble_skip * 4);

        return -EINVAL;
    }

    /*
     * PACIASP/PACIBSP must not execute before branching to the
     * replacement function. Preserve a valid BTI landing pad instead.
     */
    if (preamble_skip > 0 && ksu_insn_is_pac_signing(fn0_insn))
        insn_at_fn0 = fn0_insn;

    branch_b = ksu_encode_b(patch_addr, new_fn);

    if (!branch_b) {
        mutex_unlock(&ksu_site_lock);

        pr_err("KSU: RKP branch target out of range: %pS -> %pS\n",
               patch_addr, new_fn);

        return -ERANGE;
    }

    stub_idx = ksu_stub_next;
    stub = (u8 *)ksu_stub_page + stub_idx * KSU_STUB_SIZE;

    /*
     * Stub layout:
     * [0] KCFI hash
     * [1] BTI landing pad
     * [2] displaced original instruction
     * [3] branch back to the original function
     */
    stub_instructions[0] =
        READ_ONCE(*((u32 *)current_fn - 1));

    stub_instructions[1] =
        insn_at_fn0 ? 0xD503245F : 0xD503245F;

    stub_instructions[2] = insn_at_patch;

    stub_instructions[3] = ksu_encode_b(
        (u8 *)stub + 12, stub_resume);

    if (!stub_instructions[3]) {
        mutex_unlock(&ksu_site_lock);

        pr_err("KSU: RKP stub resume branch out of range\n");
        return -ERANGE;
    }

    /*
     * The stub is not reachable yet. Write it through the same
     * KSU-Next patching path used for protected kernel text.
     */
    ret = ksu_rkp_write_stub(stub, stub_instructions);

    if (ret) {
        mutex_unlock(&ksu_site_lock);

        pr_err("KSU: RKP stub write failed: %d\n", ret);
        return ret;
    }

    /*
     * Commit the function-entry and branch changes together.
     */
    if (insn_at_fn0) {
        patch_addresses[0] = current_fn;
        patch_addresses[1] = patch_addr;

        {
            u32 patch_instructions[2] = {
                0xD503245F,
                branch_b,
            };

            ret = ksu_rkp_patch_words(
                patch_addresses,
                patch_instructions,
                2);
        }
    } else {
        patch_addresses[0] = patch_addr;

        ret = ksu_rkp_patch_words(
            patch_addresses,
            &branch_b,
            1);
    }

    if (ret) {
        mutex_unlock(&ksu_site_lock);

        pr_err("KSU: RKP branch installation failed: %d\n", ret);
        return ret;
    }

    ksu_sites[ksu_site_count++] = (struct ksu_branch_site) {
        .fn_addr = current_fn,
        .insn_at_patch = insn_at_patch,
        .insn_at_fn0 = insn_at_fn0,
        .stub_idx = stub_idx,
        .preamble_skip = preamble_skip,
    };

    ksu_stub_next++;

    pr_info("KSU: RKP branch installed: %pS -> %pS (stub %d)\n",
            current_fn, new_fn, stub_idx);

    mutex_unlock(&ksu_site_lock);
    return 0;
}

void *ksu_rkp_get_stub(void *fn)
{
    struct ksu_branch_site *site;
    void *result = NULL;

    mutex_lock(&ksu_site_lock);

    site = ksu_find_site(fn);

    if (site && ksu_stub_page) {
        result = (u8 *)ksu_stub_page +
                 site->stub_idx * KSU_STUB_SIZE + sizeof(u32);
    }

    mutex_unlock(&ksu_site_lock);

    return result;
}

void ksu_rkp_branch_exit(void)
{
    mutex_lock(&ksu_site_lock);

    if (ksu_stub_page) {
        set_memory_nx((unsigned long)ksu_stub_page, 1);
        ksu_exec_free(ksu_stub_page);

        ksu_stub_page = NULL;
        ksu_stub_next = 0;
    }

    ksu_site_count = 0;

    mutex_unlock(&ksu_site_lock);
}

void rkp_jb_exit(void)
{
    ksu_rkp_branch_exit();
    static_branch_disable(&ksu_rkp_key);
}

#else /* !__aarch64__ */

void rkp_jb_exit(void)
{
    static_branch_disable(&ksu_rkp_key);
}

int ksu_rkp_branch_patch(void *dst, void *src)
{
    return -ENOSYS;
}

void *ksu_rkp_get_stub(void *fn)
{
    return NULL;
}

#endif /* __aarch64__ */
