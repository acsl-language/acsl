//NOPP-BEGIN
#include <stdlib.h> 
//NOPP-END
//@ ghost int heap_status;
/*@ axiomatic dynamic_allocation {
  @   predicate is_allocable(size_t n) // Can a block of n bytes be allocated?
  @               reads heap_status; 
  @  }
  @*/
 
/*@ allocates \result;
  @ behavior allocation:
  @   assumes   is_allocable(n);
  @   assigns   heap_status;
  @   ensures   \fresh(\result,n);
  @ behavior no_allocation:
  @   assumes   !is_allocable(n);
  @   assigns   \nothing;
  @   allocates \nothing;
  @   ensures   \result==\null;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void *malloc(size_t n);

/*@ frees p;
  @ behavior deallocation:
  @   assumes  p!=\null;
  @   requires \freeable(p);
  @   assigns  heap_status;
  @   ensures  \allocable(p);
  @ behavior no_deallocation:
  @   assumes  p==\null;
  @   assigns  \nothing;
  @   frees    \nothing;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void free(void *p);
