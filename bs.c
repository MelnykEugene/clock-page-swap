// =================================================================================================================================
/**
 * bs.c
 *
 * Provide a backing store for expanded memory capacity.
 **/
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <sys/mman.h>
#include "bs.h"
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS AND MACRO FUNCTIONS

#define KB(n)      (n * 1024)
#define MB(n)      (KB(n) * 1024)
#define GB(n)      (MB(n) * 1024)
 
#define DEFAULT_BACKING_STORE_SIZE GB(1)
#define BLOCK_SIZE                 KB(4)

static void*        bs_base        = NULL;
static void*        bs_limit       = NULL;
static uint64_t     bs_size        = DEFAULT_BACKING_STORE_SIZE;
// =================================================================================================================================



// =================================================================================================================================
void
bs_init () {

  // Only initialize if it hasn't already happened.
  if (bs_base == NULL) {

    // Determine the backing store size, preferrably by environment variable, otherwise use the default.
    char* bs_size_envvar = getenv("VMSIM_BS_SIZE");
    if (bs_size_envvar != NULL) {
      errno = 0;
      bs_size = strtoul(bs_size_envvar, NULL, 10);
      assert(errno == 0);
    }

    // Map the backing store space.
    bs_base = mmap(NULL, bs_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(bs_base != NULL);
    bs_limit = (void*)((intptr_t)bs_base + bs_size);
		   
  }
  
}



void*
get_block_ptr (unsigned int block_number) {

  // Calculate where requested block starts.
  void* block_ptr = (void*)((intptr_t)bs_base + (block_number * BLOCK_SIZE));

  // Don't allow a pointer that is off the end of the device.
  if (block_ptr >= bs_limit) {
    block_ptr = NULL;
  }

  return block_ptr;

}



bool
bs_read (vmsim_addr_t buffer, unsigned int block_number) {

  // Get the block pointer, and check if its valid.
  void* block_ptr = get_block_ptr(block_number);
  if (block_ptr == NULL) {
    return false;
  }

  // Copy the block into real memory.
  vmsim_write_real(block_ptr, buffer, BLOCK_SIZE);
  return true;
  
} // bs_read ()



bool
bs_write (vmsim_addr_t buffer, unsigned int block_number) {

  // Get the block pointer, and check if its valid.
  void* block_ptr = get_block_ptr(block_number);
  if (block_ptr == NULL) {
    return false;
  }

  // Copy the block into real memory.
  vmsim_read_real(block_ptr, buffer, BLOCK_SIZE);
  return true;
  
} // bs_write ()
// =================================================================================================================================
