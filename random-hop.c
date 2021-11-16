// =================================================================================================================================
/**
 * \file   random-hop.c
 * \brief  Within a simulated space, jump randomly to locations, marking each and ending when a location is revisited.
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

#if !defined (RH_DEBUG)
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

  fprintf(stderr, "USAGE: %s <space size (bytes)>\n", invocation);
  exit(1);
  
} // show_usage_and_exit ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * \brief Randomly visit simulated addresses, marking locations until an already-marked one is visited.
 * \param size The number of bytes in the space to be randomly visited.
 */
void
go (unsigned int size) {

  // Randomly select locations within the given space.
  char buffer;
  unsigned int reps = 0;
  while (true) {

    reps += 1;
    unsigned int addr = random() % size;
    if (debug) fprintf(stderr, "DEBUG:\tgo():\tVisiting address 0x%x\n", addr);
    vmsim_read(&buffer, addr, sizeof(buffer));
    if (buffer != 0) {
      break;
    }
    buffer = 1;
    vmsim_write(&buffer, addr, sizeof(buffer));

  }

  printf("Total reps: %d\n", reps);
  
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
  if (argc != 2) {
    show_usage_and_exit(argv[0]);
  }

  // Extract the arguments.
  errno = 0;
  unsigned int size = atoi(argv[1]);
  if (errno != 0 || size < 0) {
    show_usage_and_exit(argv[0]);
  }

  go(size);
  
  
} // main ()
// =================================================================================================================================
