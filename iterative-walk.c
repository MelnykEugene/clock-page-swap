// =================================================================================================================================
/**
 * \file   iterative-walk.c
 * \brief  Create an array, and iterate over it.  Use the `vmsim` library for the array.
 * \author Prof. Scott F. Kaplan
 * \date   Fall 2018
 **/
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS AND MACRO FUNCTIONS

/** The number of bytes in an kilobyte. */
#define BYTES_PER_KB 1024
// =================================================================================================================================



// =================================================================================================================================
// GLOBALS

#if !defined (IW_DEBUG)
static bool debug = false;
#else
static bool debug = true;
#endif
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief Display the proper usage and end the process with an error code.
 * \param invocation The command-line text given to run the executable.
 */
void
show_usage_and_exit (char* invocation) {

  fprintf(stderr, "USAGE: %s <data size (array length)> <iterations>\n", invocation);
  exit(1);
  
} // show_usage_and_exit ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief Initialize an array with values such that each entry contains its own index.
 * \param array  The simulated address of an array of unsigned 64-bit integers.
 * \param length The number of elements in the array.
 */
void
populate (vmsim_addr_t array, unsigned int length) {

  // Set it spot in the array to store its own index.
  for (uint64_t i = 0; i < length; i += 1) {

    vmsim_addr_t addr = array + (i * sizeof(i));
    vmsim_write(&i, addr, sizeof(i));
    if (debug) {
      uint64_t value;
      vmsim_read(&value, addr, sizeof(value));
      fprintf(stderr, "DEBUG:\tpopulate():\t0x%x[%ld] = %ld\n", array, i, value);
    }

  }
  
} // populate ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief Move through the array, summing the values found and storing the running sum into each position.
 * \param array  The simulated address of an array of unsigned 64-bit integers.
 * \param length The number of elements in the array.
 */
void
traverse (vmsim_addr_t array, unsigned int length) {

  // Progressively sum over the array, overflow be damned.
  uint64_t sum = 0;
  for (uint64_t i = 0; i < length; i += 1) {

    vmsim_addr_t addr = array + (i * sizeof(i));
    uint64_t current;
    vmsim_read(&current, addr, sizeof(current));
    sum += current;
    vmsim_write(&sum, addr, sizeof(sum));
    if (debug) {
      fprintf(stderr, "DEBUG:\ttraverse():\t0x%x[%ld] <- %ld -> %ld\n", array, i, sum, current);
    }
    
  }
  
} // traverse ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief Create an array, initiialize it, and then traverse it repeatedly.
 * \param length     The size of the array to create.
 * \param iterations The number of traversals to perform on the array.
 */
void
go (unsigned int length, unsigned int iterations) {

  // Allocate the array.
  vmsim_addr_t array = vmsim_alloc(length * sizeof(uint64_t));
  assert(array != 0);

  // Populate the array.
  populate(array, length);

  // Sum over the array the requested number of times.
  for (int i = 0; i < iterations; i += 1) {
    traverse(array, length);
  }

  // Show the final thing.
  uint64_t     value;
  vmsim_addr_t addr  = array + ((length - 1) * sizeof(value));
  vmsim_read(&value, addr, sizeof(value));
  printf("%ld\n", value);
  
  // Clean up.
  vmsim_free(array);
  
} // go ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief The entry point to the simulator.
 * \param argc The length of the command-line argument vector.
 * \param argv The vector of command-line arguments.
 * \return the exit code for the process, where 0 indicates success, any other value indicates error.
 */
int
main (int argc, char** argv) {

  // Check usage.
  if (argc != 3) {
    show_usage_and_exit(argv[0]);
  }

  // Extract the arguments.
  errno = 0;
  unsigned int length = atoi(argv[1]);
  if (errno != 0 || length < 0) {
    show_usage_and_exit(argv[0]);
  }

  errno = 0;
  unsigned int iterations = atoi(argv[2]);
  if (errno != 0 || iterations < 1) {
    show_usage_and_exit(argv[0]);
  }
  
  go(length, iterations);
  
  
} // main ()
// =================================================================================================================================
