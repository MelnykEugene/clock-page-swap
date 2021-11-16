// =================================================================================================================================
/**
 * mmu.c
 */
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "mmu.h"
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// MACROS AND GLOBALS

#define GET_UPPER_INDEX(addr) ((addr >> 22) & 0x3ff)
#define GET_LOWER_INDEX(addr) ((addr >> 12) & 0x3ff)
#define GET_OFFSET(addr)      (addr & 0xfff)
#define GET_PAGE_ADDR(addr)   (addr & ~0xfff)
#define IS_RESIDENT(pte)      (pte & PTE_RESIDENT_BIT)
#define SET_REFERENCED(pte)   (pte |= PTE_REFERENCED_BIT)
#define SET_DIRTY(pte)        (pte |= PTE_DIRTY_BIT)

static vmsim_addr_t upper_pt_addr = 0;

#if !defined (MMU_DEBUG)
static bool debug = false;
#else
static bool debug = true;
#endif
// =================================================================================================================================



// =================================================================================================================================
void
mmu_init (vmsim_addr_t new_upper_pt_addr) {

  upper_pt_addr = new_upper_pt_addr;
  
}
// =================================================================================================================================



// =================================================================================================================================
vmsim_addr_t
mmu_translate (vmsim_addr_t sim_addr, bool write_operation) {

  if (debug) fprintf(stderr, "DEBUG:\tmmu_translate():\tEntry on sim_addr = %8x\n", sim_addr);
  
  // Sanity check:  There must be a page-table from which to start.
  assert(upper_pt_addr != 0);

  // Grab the upper table's entry.
  vmsim_addr_t upper_index    = GET_UPPER_INDEX(sim_addr);
  vmsim_addr_t upper_pte_addr = upper_pt_addr + (upper_index * sizeof(pt_entry_t));
  pt_entry_t   upper_pte      = 0;
  vmsim_read_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));

  if (debug) fprintf(stderr, "DEBUG:\tmmu_translate():\tupper_pte = %8x\n", upper_pte);

  // If the lower table doesn't exist, trigger a mapping and restart.
  if (upper_pte == 0) {
    vmsim_map_fault(sim_addr);
    return mmu_translate(sim_addr, write_operation);
  }

  // Get the pointer to the lower table.
  vmsim_addr_t lower_pt_addr = GET_PAGE_ADDR(upper_pte);

  // Grab the lower table's entry.
  vmsim_addr_t lower_index    = GET_LOWER_INDEX(sim_addr);
  vmsim_addr_t lower_pte_addr = lower_pt_addr + (lower_index * sizeof(pt_entry_t));
  pt_entry_t   lower_pte      = 0;
  vmsim_read_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));

  if (debug) fprintf(stderr, "DEBUG:\tmmu_translate():\tlower_pte = %8x\n", lower_pte);
  
  // If the page is unmapped, or if it is mapped and not resident, then trigger a fault and restart.
  if ((lower_pte == 0) || !IS_RESIDENT(lower_pte)) {
    vmsim_map_fault(sim_addr);
    return mmu_translate(sim_addr, write_operation);
  }

  // Set the reference bit and, if appropriate, the dirty bit.
  SET_REFERENCED(lower_pte);
  if (write_operation) {
    SET_DIRTY(lower_pte);
  }
  vmsim_write_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));
  
  // Glue together the simulated page address and the offset.
  vmsim_addr_t real_addr = GET_PAGE_ADDR(lower_pte) | GET_OFFSET(sim_addr);
  if (debug) fprintf(stderr, "DEBUG:\tmmu_translate():\t%x -> %x\n", sim_addr, real_addr);
  return real_addr;
  
}
// =================================================================================================================================
