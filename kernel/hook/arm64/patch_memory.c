/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Copyright (C) 2023 bmax121. All Rights Reserved.
 */

#ifdef __aarch64__

#include "../patch_memory.h"
#include "klog.h" // IWYU pragma: keep

#include <linux/cpumask.h>
#include <linux/errno.h>
#include <linux/gfp.h> // IWYU pragma: keep
#include <linux/kernel.h>
#include <linux/limits.h>
#include <linux/mm.h>
#include <linux/stop_machine.h>
#include <linux/uaccess.h>

#include <asm/cacheflush.h>
#include <asm-generic/fixmap.h>

// Translate a kernel virtual address to a physical address by walking
// the init_mm page tables. Physical address 0 is valid; callers must
// inspect *err to determine whether translation succeeded.
unsigned long phys_from_virt(unsigned long addr, int *err)
{
    struct mm_struct *mm = &init_mm;
    pgd_t *pgd;
    p4d_t *p4d;
    pud_t *pud;
    pmd_t *pmd;
    pte_t *pte;

    *err = 0;

    pgd = pgd_offset(mm, addr);
    if (pgd_none(*pgd) || pgd_bad(*pgd))
        goto fail;

    p4d = p4d_offset(pgd, addr);
    if (p4d_none(*p4d) || p4d_bad(*p4d))
        goto fail;

#if defined(p4d_leaf)
    if (p4d_leaf(*p4d))
        return __p4d_to_phys(*p4d) + (addr & ~P4D_MASK);
#endif

    pud = pud_offset(p4d, addr);
    if (pud_none(*pud) || pud_bad(*pud))
        goto fail;

#if defined(pud_leaf)
    if (pud_leaf(*pud))
        return __pud_to_phys(*pud) + (addr & ~PUD_MASK);
#endif

    pmd = pmd_offset(pud, addr);

#if defined(pmd_leaf)
    if (pmd_leaf(*pmd))
        return __pmd_to_phys(*pmd) + (addr & ~PMD_MASK);
#endif

    if (pmd_none(*pmd) || pmd_bad(*pmd))
        goto fail;

    pte = pte_offset_kernel(pmd, addr);
    if (!pte || !pte_present(*pte))
        goto fail;

    return __pte_to_phys(*pte) + (addr & ~PAGE_MASK);

fail:
    *err = -ENOENT;
    return 0;
}

// Detect the available D-cache flush implementation.
#if KSU_NEW_DCACHE_FLUSH

#define ksu_flush_dcache(start, sz)                                      \
    ({                                                                   \
        unsigned long __start = (unsigned long)(start);                  \
        unsigned long __end = __start + (sz);                            \
        dcache_clean_inval_poc(__start, __end);                          \
    })

#define ksu_flush_icache(start, end) caches_clean_inval_pou(start, end)

#else

#define ksu_flush_dcache(start, sz) __flush_dcache_area((void *)start, sz)
#define ksu_flush_icache(start, end) __flush_icache_range(start, end)

#endif

#define KSU_PATCH_VALID_FLAGS \
    (KSU_PATCH_TEXT_FLUSH_DCACHE | KSU_PATCH_TEXT_FLUSH_ICACHE)

struct patch_text_info {
    const struct ksu_patch_entry *entries;
    size_t count;
    atomic_t cpu_count;
    int ret;
};

/*
 * Validate the complete destination range before entering stop_machine.
 *
 * Every virtual page is translated separately. This also handles ranges
 * backed by huge-page mappings through phys_from_virt().
 */
static int ksu_patch_text_validate_range(void *dst, size_t len)
{
    unsigned long addr = (unsigned long)dst;
    size_t remaining = len;

    if (!dst || !len)
        return -EINVAL;

    if (len > ULONG_MAX - addr)
        return -EOVERFLOW;

    while (remaining) {
        unsigned long phy;
        size_t chunk;
        int err;

        phy = phys_from_virt(addr, &err);
        if (err)
            return err;

        chunk = min_t(size_t, remaining,
                      PAGE_SIZE - (addr & ~PAGE_MASK));

        addr += chunk;
        remaining -= chunk;
    }

    return 0;
}

static int ksu_patch_text_validate_entries(
    const struct ksu_patch_entry *entries,
    size_t count)
{
    size_t i;

    if (!entries || !count)
        return -EINVAL;

    for (i = 0; i < count; i++) {
        const struct ksu_patch_entry *entry = &entries[i];
        int ret;

        if (!entry->dst || !entry->src || !entry->len)
            return -EINVAL;

        if (entry->flags & ~KSU_PATCH_VALID_FLAGS)
            return -EINVAL;

        ret = ksu_patch_text_validate_range(entry->dst, entry->len);
        if (ret)
            return ret;
    }

    return 0;
}

/*
 * Copy one entry through fixmap.
 *
 * The copy is split at virtual page boundaries. Each chunk is translated
 * independently, so no fixmap mapping is used beyond its mapped page.
 *
 * This function runs under stop_machine on the master CPU.
 */
static int ksu_patch_text_nosync(
    const struct ksu_patch_entry *entry)
{
    unsigned long dst = (unsigned long)entry->dst;
    const char *src = (const char *)entry->src;
    size_t remaining = entry->len;
    int ret = 0;

    while (remaining) {
        unsigned long phy;
        size_t chunk;
        void *map;
        int phy_err;

        phy = phys_from_virt(dst, &phy_err);
        if (phy_err) {
            ret = phy_err;
            break;
        }

        chunk = min_t(size_t, remaining,
                      PAGE_SIZE - (dst & ~PAGE_MASK));

        map = set_fixmap_offset(FIX_TEXT_POKE0, phy);

        ret = copy_to_kernel_nofault(map, src, chunk);

        clear_fixmap(FIX_TEXT_POKE0);

        if (ret)
            break;

        dst += chunk;
        src += chunk;
        remaining -= chunk;
    }

    /*
     * Flush the complete destination range even on an error.
     * A failed nofault copy must not leave potentially modified bytes
     * with stale instruction or data caches.
     */
    if (entry->flags & KSU_PATCH_TEXT_FLUSH_ICACHE) {
        ksu_flush_icache((uintptr_t)entry->dst,
                         (uintptr_t)entry->dst + entry->len);
    }

    if (entry->flags & KSU_PATCH_TEXT_FLUSH_DCACHE)
        ksu_flush_dcache(entry->dst, entry->len);

    return ret;
}

/*
 * Execute all entries on the master CPU while the other CPUs remain
 * stopped inside the same stop_machine operation.
 *
 * A batch is not a rollback-capable transaction: if a later write fails,
 * earlier successful writes are not automatically reverted.
 */
static int ksu_patch_text_cb(void *arg)
{
    struct patch_text_info *info = arg;

    /* The last CPU becomes master. */
    if (atomic_inc_return(&info->cpu_count) == num_online_cpus()) {
        size_t i;

        info->ret = 0;

        for (i = 0; i < info->count; i++) {
            info->ret = ksu_patch_text_nosync(&info->entries[i]);
            if (info->ret) {
                pr_err("KSU: batch patch failed at entry %zu, address 0x%lx: %d\n",
                       i,
                       (unsigned long)info->entries[i].dst,
                       info->ret);
                break;
            }
        }

        /*
         * Ensure instruction synchronization on the master CPU too.
         */
        isb();

        /* Release the waiting CPUs. */
        atomic_inc(&info->cpu_count);

        return info->ret;
    }

    while (atomic_read(&info->cpu_count) <= num_online_cpus())
        cpu_relax();

    isb();

    return 0;
}

/*
 * Patch multiple kernel address ranges in one stop_machine operation.
 */
int ksu_patch_text_batch(
    const struct ksu_patch_entry *entries,
    size_t count)
{
    struct patch_text_info info;
    int ret;

    ret = ksu_patch_text_validate_entries(entries, count);
    if (ret) {
        pr_err("KSU: batch patch validation failed: %d\n", ret);
        return ret;
    }

    info.entries = entries;
    info.count = count;
    info.cpu_count = ATOMIC_INIT(0);
    info.ret = 0;

    ret = stop_machine(ksu_patch_text_cb, &info, cpu_online_mask);

    if (ret)
        pr_err("KSU: stop_machine batch patch failed: %d\n", ret);

    return ret;
}

/*
 * Backward-compatible single-range interface.
 */
int ksu_patch_text(void *dst, void *src, size_t len, int flags)
{
    const struct ksu_patch_entry entry = {
        .dst = dst,
        .src = src,
        .len = len,
        .flags = flags,
    };

    return ksu_patch_text_batch(&entry, 1);
}

/*
 * Scan [start, start + size) for a BL instruction whose branch target
 * equals target.
 *
 * AArch64 BL encoding:
 * bits[31:26] = 0b100101
 * bits[25:0]  = imm26
 *
 * Branch target = PC + SignExtend(imm26, 26) * 4.
 */
void *scan_call_to(void *start, size_t size, void *target)
{
    const uint32_t *insn = (const uint32_t *)start;
    size_t count = size / sizeof(uint32_t);
    size_t i;

    for (i = 0; i < count; i++) {
        int32_t imm26;
        void *branch_target;

        if ((insn[i] & 0xFC000000U) != 0x94000000U)
            continue;

        imm26 = (int32_t)((insn[i] & 0x03FFFFFFU) << 6) >> 6;

        branch_target = (void *)((uintptr_t)&insn[i] +
                                 ((int64_t)imm26 << 2));

        if (branch_target == target)
            return (void *)&insn[i];
    }

    return NULL;
}

#endif /* __aarch64__ */
