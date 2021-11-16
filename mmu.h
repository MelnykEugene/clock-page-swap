/**
 * \file   mmu.h
 * \brief  The interface for the MMU module.
 * \author Prof. Scott F. Kaplan
 * \date   Fall 2018
 *
 * A simple module that is part of the `vmsim` library.  This module implements the simulated _memory management unit (MMU)_ that
 * typically provides hardware mapping of virtual-to-physical addresses.
 */

// =================================================================================================================================
// Avoid multiple inclusion.

#if !defined (_MMU_H)
#define _MMU_H
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <stdbool.h>
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// FUNCTIONS

/**
 * \brief Initialize the MMU.
 * \param upper_pt_addr The real base address of the upper page table.
 *
 * This function stores the given real address of the upper page table.  Doing so is analogous to setting a hardware MMU's _page
 * table register (PTR)_ with the physical base address of the upper PT.
 */
void         mmu_init      (vmsim_addr_t upper_pt_addr);

/**
 * \brief  Translate a simulated address into a physical address.
 * \param  sim_addr        The simulated address to be translated.
 * \param  write_operation Whether the data at the given address is being _read_ (`false`) or _written_ (`true`).
 * \return the real address to which the simulated address maps.
 *
 * This function walks the multi-level page table to find the mapping from the given simulated address to its corresponding real
 * address.  If the simulated address is not yet mapped to a real address, then this function calls `vmsim_map_fault()` (mimicking
 * an _address translation interrupt_, or _page fault_, in hardware) to have the mapping created, and then restarts the translation.
 */
vmsim_addr_t mmu_translate (vmsim_addr_t sim_addr, bool write_operation);
// =================================================================================================================================



// =================================================================================================================================
#endif // _MMU_H
// =================================================================================================================================
