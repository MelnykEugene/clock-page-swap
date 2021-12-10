// =================================================================================================================================
/**
 * vmsim.c
 *
 * Allocate space that is then virtually mapped, page by page, to a simulated underlying space.  Maintain page tables and follow
 * their mappings with a simulated MMU.
 **/
// ================================================================================================================================


// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include "bs.h"
#include "mmu.h"
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS AND MACRO FUNCTIONS

#define KB(n)      (n * 1024)
#define MB(n)      (KB(n) * 1024)
#define GB(n)      (MB(n) * 1024)
 
#define DEFAULT_REAL_MEMORY_SIZE   MB(5)
#define PAGESIZE                   KB(4)
#define PT_AREA_SIZE               (MB(4) + KB(4))

#define OFFSET_MASK           (PAGESIZE - 1)
#define PAGE_NUMBER_MASK      (~OFFSET_MASK)
#define GET_UPPER_INDEX(addr) ((addr >> 22) & 0x3ff)
#define GET_LOWER_INDEX(addr) ((addr >> 12) & 0x3ff)
#define GET_OFFSET(addr)      (addr & OFFSET_MASK)
#define GET_PAGE_ADDR(addr)   (addr & PAGE_NUMBER_MASK)
#define IS_ALIGNED(addr)      ((addr & OFFSET_MASK) == 0)

#define IS_RESIDENT(pte)      (pte & PTE_RESIDENT_BIT)
#define IS_REFERENCED(pte)    (pte & PTE_REFERENCED_BIT)
#define IS_DIRTY(pte)         (pte & PTE_DIRTY_BIT)
#define SET_RESIDENT(pte)     (pte |= PTE_RESIDENT_BIT)
#define CLEAR_RESIDENT(pte)   (pte &= ~PTE_RESIDENT_BIT)
#define CLEAR_REFERENCED(pte) (pte &= ~PTE_REFERENCED_BIT)
#define CLEAR_DIRTY(pte)      (pte &= ~PTE_DIRTY_BIT)

// The boundaries and size of the real memory region.
static void*        real_base      = NULL;
static void*        real_limit     = NULL;
static uint64_t     real_size      = DEFAULT_REAL_MEMORY_SIZE;

// Where to find the next page of real memory for page table blocks.
static vmsim_addr_t pt_free_addr   = PAGESIZE;

// Where to find the next page of real memory for backing simulated pages.
static vmsim_addr_t real_free_addr = PT_AREA_SIZE;

// The base real address of the upper page table.
static vmsim_addr_t upper_pt       = 0;

// Used by the heap allocator, the address of the next free simulated address.
static vmsim_addr_t sim_free_addr  = 0;

// Will be the list of all in-memory pages
static pt_entry_t** pages = NULL;

// possible number of current real pages
static uint64_t number_of_entries = (DEFAULT_REAL_MEMORY_SIZE - PT_AREA_SIZE)/PAGESIZE;

// "clock handle"
static uint64_t current_page_number = 0;

// number of next avaliable block on the backing store for pointer bumping
static uint64_t next_block_number = 1;

// =================================================================================================================================

pt_entry_t*  find_lru();
vmsim_addr_t send_to_back_and_give_address (pt_entry_t* entry_pointer);
void         bring_back (vmsim_addr_t entry_address, vmsim_addr_t real_address);
void         swap(vmsim_addr_t backing_store_address, pt_entry_t* real_page);

// =================================================================================================================================
/**
 * Allocate a page of real memory space for a page table block.  Taken from a region of real memory reserved for this purpose.
 *
 * \return The _real_ base address of a page of memory for a page table block.
 */
vmsim_addr_t
allocate_pt () {

  vmsim_addr_t new_pt_addr = pt_free_addr;
  pt_free_addr += PAGESIZE;
  assert(IS_ALIGNED(new_pt_addr));
  assert(pt_free_addr <= PT_AREA_SIZE);
  void* new_pt_ptr = (void*)(real_base + new_pt_addr);
  memset(new_pt_ptr, 0, PAGESIZE);
  
  return new_pt_addr;
  
} // allocate_pt ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Allocate a page of real memory space for backing a simulated page.  Taken from the general pool of real memory.
 *
 * \return The _real_ base address of a page of memory.
 */
vmsim_addr_t
allocate_real_page () {
  //the original template for this function made no sense to me. I think it would fail assertions after free memory was all used for the first time. Rewrote the logic
  
    vmsim_addr_t new_real_addr = real_free_addr;
    real_free_addr += PAGESIZE;
    assert(IS_ALIGNED(new_real_addr));

  //if we are out of memory,swap
  //Note that we never amend our changes to real_free_addr. In the absence of reclamation, this should be fine. Once we run out of memory, we stay out of memory.
  if (real_free_addr > real_size) {
    
    pt_entry_t* entry = find_lru();
    vmsim_addr_t freed_address = send_to_back_and_give_address(entry);
    return freed_address;

  } 
  //otherwise the address we obtained by bumping is good:
  
  void* new_real_ptr = (void*)(real_base + new_real_addr);
  memset(new_real_ptr, 0, PAGESIZE);
  return new_real_addr;
  
} // allocate_real_page ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_init () {

  // Only initialize if it hasn't already happened.
  if (real_base == NULL) {

    // Determine the real memory size, preferrably by environment variable, otherwise use the default.
    char* real_size_envvar = getenv("VMSIM_REAL_MEM_SIZE");
    if (real_size_envvar != NULL) {
      errno = 0;
      real_size = strtoul(real_size_envvar, NULL, 10);
      assert(errno == 0);
    }

    // Map the real storage space.
    real_base = mmap(NULL, real_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(real_base != NULL);
    real_limit = (void*)((intptr_t)real_base + real_size);
    upper_pt = allocate_pt();

    // Initialize the simualted space allocator.  Leave page 0 unused, start at page 1.
    sim_free_addr = PAGESIZE;

    // Initialize the supporting components.
    mmu_init(upper_pt);
    bs_init();
    
    //initialize the clock
    number_of_entries = (real_size - PT_AREA_SIZE)/PAGESIZE;
    pages = malloc(number_of_entries * sizeof(vmsim_addr_t));
  }
  
} // vmsim_init ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Map a _simulated_ address to a _real_ one, ensuring first that the page table and real spaces are initialized.
 *
 * \param  sim_addr        The _simulated_ address to translate.
 * \param  write_operation Whether the memory access is to _read_ (`false`) or to _write_ (`true`).
 * \return the translated _real_ address.
 */ 
vmsim_addr_t
vmsim_map (vmsim_addr_t sim_addr, bool write_operation) {

  vmsim_init();

  assert(real_base != NULL);
  vmsim_addr_t real_addr = mmu_translate(sim_addr, write_operation);
  return real_addr;
  
} // vmsim_map ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Called when the translation of a _simulated_ address fails.  When this function is done, a _real_ page will back the _simulated_
 * one that contains the given address, with the page tables appropriately updated.
 *
 * \param sim_addr The _simulated_ address for which address translation failed.
 */
void
vmsim_map_fault (vmsim_addr_t sim_addr) {

  assert(upper_pt != 0);

  // Grab the upper table's entry.
  vmsim_addr_t upper_index    = GET_UPPER_INDEX(sim_addr);
  vmsim_addr_t upper_pte_addr = upper_pt + (upper_index * sizeof(pt_entry_t));
  pt_entry_t   upper_pte;
  vmsim_read_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));

  // If the lower table doesn't exist, create it and update the upper table.
  if (upper_pte == 0) {

    upper_pte = allocate_pt();
    assert(upper_pte != 0);
    vmsim_write_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));
  }

  // Grab the lower table's entry.
  vmsim_addr_t lower_pt       = GET_PAGE_ADDR(upper_pte);
  vmsim_addr_t lower_index    = GET_LOWER_INDEX(sim_addr);
  vmsim_addr_t lower_pte_addr = lower_pt + (lower_index * sizeof(pt_entry_t));
  pt_entry_t   lower_pte;
  vmsim_read_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));

  // If there is no mapped page, create it and update the lower table.
  // we only allocate if there is no mapped page, else we handle this in swap
  // I think i dublicated some logic somewhere. what can you do
  // Update: Yeah, a neater way would be to hide this logic within allocate_real_page. This bleeds abstraction for no reason but I don't have time to rewrite.
  // SK: Agreed.  
  if (lower_pte == 0) {    
    lower_pte = allocate_real_page();
    SET_RESIDENT(lower_pte);
    vmsim_write_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));

  }  else if (!IS_RESIDENT(lower_pte)) {

    pt_entry_t* to_swap_out = find_lru();
    swap(lower_pte_addr,to_swap_out);
    
  }
  
} // vmsim_map_fault ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_read_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*)((intptr_t)ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes from the real space.
  memcpy(buffer, ptr, size);
  
} // vmsim_read_real ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_write_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*)((intptr_t)ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes into the real space.
  memcpy(ptr, buffer, size);
  
} // vmsim_write_real ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_read (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, false);
  vmsim_read_real(buffer, real_addr, size);

} // vmsim_read ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_write (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, true);
  vmsim_write_real(buffer, real_addr, size);

} // vmsim_write ()
// =================================================================================================================================



// =================================================================================================================================
vmsim_addr_t
vmsim_alloc (size_t size) {

  vmsim_init();

  // Pointer-bumping allocator with no reclamation.
  vmsim_addr_t addr = sim_free_addr;
  sim_free_addr += size;
  return addr;
  
} // vmsim_alloc ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_free (vmsim_addr_t ptr) {

  // No relcamation, so nothing to do.

} // vmsim_free ()
// =================================================================================================================================








// =================================================================================================================================
pt_entry_t*
find_lru(){

  //get the clock handle
  pt_entry_t current = *pages[current_page_number];

  //go alongside the clock and set the visited pages as cold. Replace them as such in the real memory
  while IS_REFERENCED(current){

    //make a copy of the current address, but flagged cold
    pt_entry_t current_cleared_copy = CLEAR_REFERENCED(current);

    //vsvim_write_real wants an adress RELATIVE to the real_base
    //!!!
    vmsim_addr_t address_to_rewrite = (vmsim_addr_t)( (void*) pages[current_page_number] - real_base);

    vmsim_write_real(&current_cleared_copy,address_to_rewrite,sizeof(pt_entry_t));

    //iterate the clock
    current_page_number = (current_page_number + 1)% number_of_entries;
    current = *pages[current_page_number];
  }
  return pages[current_page_number];

} // find_lru())
// =================================================================================================================================








// =================================================================================================================================
void
swap (vmsim_addr_t backing_store_address, pt_entry_t* real_page) {

  vmsim_addr_t freed_page = send_to_back_and_give_address(real_page);

  bring_back(backing_store_address, freed_page);

} // swap ()
// =================================================================================================================================










// =================================================================================================================================
//Given a (pointer to) LPT entry, send the contents to the back store and gives a real (FREE) address
vmsim_addr_t send_to_back_and_give_address(pt_entry_t* entry_pointer){
  
  pt_entry_t entry = *entry_pointer;
  vmsim_addr_t real_page_address_to_swap = GET_PAGE_ADDR(entry);
  bs_write(real_page_address_to_swap,next_block_number);

  //The UPPER bits of the new entry will correspond to the BLOCK NUMBER on the backing store
  // 0x3ff = 2^10 in binary
  CLEAR_RESIDENT(entry);
  entry = (entry & 0x3ff) | (next_block_number << 10);

  next_block_number+=1;

  vmsim_addr_t address_to_rewrite = (vmsim_addr_t) ((void*) entry_pointer - real_base);
  vmsim_write_real(&entry, address_to_rewrite, sizeof(pt_entry_t));

  //at this point, the address we have is considered freed
  return real_page_address_to_swap;

}
// =================================================================================================================================









// =================================================================================================================================
//copies contents of the backing store corresponding to entry_address to (hopefully) free real_address
void bring_back(vmsim_addr_t entry_address, vmsim_addr_t real_address){

  pt_entry_t entry;
  vmsim_read_real(&entry,entry_address,sizeof(pt_entry_t));

  // SK: You're missing a couple of leading 'f' digits.
  //0xfffc00 in binary has lower ten bits zero and the rest 1
  uint64_t block_number = (entry & 0xfffc00) >> 10;
  bs_read(real_address,block_number);

  //re-build entry

  // SK: Keeping the pre-existing lower 10 bits makes no sense.  
  entry = (entry & 0x3ff) | real_address ;
  SET_RESIDENT(entry);
  vmsim_write_real(&entry,entry_address,sizeof(pt_entry_t));

  //update our clock to include the newly fetched page
  uint64_t page_number = (real_address- PT_AREA_SIZE)/PAGESIZE;
  pages[page_number]= (pt_entry_t*) (real_base + entry_address);
}
// =================================================================================================================================
