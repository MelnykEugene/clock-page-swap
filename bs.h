// =================================================================================================================================
/**
 * \file   bs.h
 * \brief  The interface for the backing store device.
 * \author Prof. Scott F. Kaplan
 * \date   Fall 2018
 */
// =================================================================================================================================



// =================================================================================================================================
// Avoid multiple inclusion.

#if !defined (_BS_H)
#define _BS_H
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <stdbool.h>
#include <stdlib.h>
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// FUNCTIONS

/**
 * \brief  Initialize the simulated backing store device.
 */
void bs_init  ();

/**
 * \brief  Read data from a block.
 * \param  buffer       The _real_ address of a space into which to copy the block's data.
 * \param  block_number The block number of the backing store to read.
 * \return whether the operation was successful.
 */
bool bs_read  (vmsim_addr_t buffer, unsigned int block_number);

/**
 * \brief  Write data to a block.
 * \param  buffer       The _real_ address of a space from which to copy the block's data.
 * \param  block_number The block number of the backing store to write.
 * \return whether the operation was successful.
 */
bool bs_write (vmsim_addr_t buffer, unsigned int block_number);
// =================================================================================================================================



// =================================================================================================================================
#endif // _BS_H
// =================================================================================================================================
