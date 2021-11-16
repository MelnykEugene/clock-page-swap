// =================================================================================================================================
/**
 * \file   vmsim.h
 * \brief  The interface for the `vmsim` library.
 * \author Prof. Scott F. Kaplan
 * \date   Fall 2018
 *
 * `vmsim` is a package that emulates a 32-bit virtual address space.  It provides a _simulated address space_ that is mapped onto a
 * _real address space_.  The real storage is created by the library, while a full 32-bit range of simulated addresses are mapped,
 * on demand, onto that real storage space, which can be of any size.  Space is created and mapped in 4 KB pages.  Access to
 * simulated storage is provided by the `vimsim_read()` and `vmsim_write()` functions.
 */
// =================================================================================================================================



// =================================================================================================================================
// Avoid multiple inclusion.

#if !defined (_VMSIM_H)
#define _VMSIM_H
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <stdint.h>
#include <stdlib.h>
// =================================================================================================================================



// =================================================================================================================================
// TYPES

/** A simulated or real address within `vmsim`. */
typedef uint32_t vmsim_addr_t;

/** A page table entry. */
typedef uint32_t pt_entry_t;
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS

#define PTE_RESIDENT_BIT   0x1
#define PTE_REFERENCED_BIT 0x2
#define PTE_DIRTY_BIT      0x4
// =================================================================================================================================



// =================================================================================================================================
// FUNCTIONS

/**
 * \brief Read data from the simulated space.
 * \param buffer A pointer to a space into which to copy data from the simulated space.
 * \param sim_addr The simulated address from which to read the data.
 * \param size The number of bytes to read, starting at the simulated address, into the buffer space.
 */
void         vmsim_read       (void* buffer, vmsim_addr_t sim_addr, size_t size);

/**
 * \brief Write data into the simulated space.
 * \param buffer A pointer to a space from which to copy data into the simulated space.
 * \param sim_addr The simulated address into which to write the data.
 * \param size The number of bytes to write, starting at the simulated address, from the buffer space.
 * 
 */
void         vmsim_write      (void* buffer, vmsim_addr_t sim_addr, size_t size); 

/**
 * \brief Read data from the real space.
 * \param buffer A pointer to a space into which to copy data from the real space.
 * \param real_addr The real address from which to read the data.
 * \param size The number of bytes to read, starting at the real address, into the buffer space.
 *
 * This function is the analog to `vmsim_read()`, except that the address given is the raw, _real_ address, thus triggering no
 * simulated-to-real mapping.
 */
void         vmsim_read_real  (void* buffer, vmsim_addr_t real_addr, size_t size);

/**
 * \brief Write data into the real space.
 * \param buffer A pointer to a space from which to copy data into the real space.
 * \param real_addr The real address into which to write the data.
 * \param size The number of bytes to write, starting at the real address, from the buffer space.
 *
 * This function is the analog to `vmsim_write()`, except that the address given is the raw, _real_ address, thus triggering no
 * simulated-to-real mapping.
 */
void         vmsim_write_real (void* buffer, vmsim_addr_t real_addr, size_t size);

/**
 * \brief Create a new simulated-to-real mapping for a simulated address.
 * \param sim_addr The simulated address for which to create the mapping.
 */
void         vmsim_map_fault  (vmsim_addr_t sim_addr);

/**
 * \brief  Allocate simulated memory space.
 * \param  size The number of bytes to allocate.
 * \return the simulated address of the a block that is at least `size` bytes in length.
 */
vmsim_addr_t vmsim_alloc      (size_t size);

/**
 * \brief Deallocate simulated memory space.
 * \param ptr The simulated address of a memory block allocated with `vmsim_alloc`.
 */
void         vmsim_free       (vmsim_addr_t ptr);
// =================================================================================================================================



// =================================================================================================================================
#endif // _VMSIM_H
// =================================================================================================================================
