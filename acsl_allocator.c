
/*@ logic int offset(char* p) reads \nothing; */

#include <stdlib.h>

#define DEFAULT_BLOCK_SIZE 1000

typedef enum _bool { false = 0, true = 1 } bool;

// forward reference
struct _memory_slice;

typedef struct _memory_block {
  //@ ghost bool        packed;
  unsigned int          size;
  unsigned int          next;
    // next index in [data] at which to put a chunk
  unsigned int          used;
    // how many bytes are used in [data], not necessarily contiguous ones
  char*                 data;
  struct _memory_slice* slice;
} memory_block;


/*@ type invariant inv_memory_block(memory_block mb) {
  @   mb.packed ==>
  @     (0 < mb.size && mb.used <= mb.next <= mb.size
  @     && offset(mb.data) == 0 && \block_length(mb.data) == mb.size)
  @ } */

/*@ predicate valid_memory_block(memory_block* mb) {
  @   \valid(mb) && mb->packed
  @ } */

typedef struct _memory_chunk {
  //@ ghost bool packed;
  unsigned int   offset;
  unsigned int   size;
  bool           free;
  memory_block*  block;
} memory_chunk;

/*@ type invariant inv_memory_chunk(memory_chunk mc) {
  @   mc.packed ==>
  @     (0 < mc.size && valid_memory_block(mc.block)
  @     && mc.offset + mc.size <= mc.block->next)
  @ } */

/*@ predicate valid_memory_chunk(memory_chunk* mc, int s) {
  @   \valid(mc) && mc->packed && mc->size == s
  @ } */

/*@ predicate used_memory_chunk(memory_chunk mc) {
  @   mc.free == false
  @ } */

/*@ predicate freed_memory_chunk(memory_chunk mc) {
  @   mc.free == true
  @ } */

typedef struct _memory_chunk_list {
  //@ ghost unsigned int     offset;
  memory_chunk*              chunk;
  struct _memory_chunk_list* next;
} memory_chunk_list;

/*@ predicate valid_memory_chunk_list
  @                  (memory_chunk_list* mcl, memory_block* mb) {
  @   \valid(mcl) && valid_memory_chunk(mcl->chunk,mcl->chunk->size) 
  @   && mcl->chunk->block == mb
  @   && (mcl->next == \null || valid_memory_chunk_list(mcl->next, mb))
  @   && mcl->offset == mcl->chunk->offset
  @   && (mcl->next == \null
  @       || mcl->next->offset + mcl->next->chunk->size == mcl->offset)
  @ } */

typedef struct _memory_slice {
  memory_block*      block;
  memory_chunk_list* chunks;
} memory_slice;

/*@ predicate valid_memory_slice(memory_slice* ms) {
  @   \valid(ms) && valid_memory_block(ms->block) && ms->block->slice == ms
  @   && (ms->chunks == \null
  @       || valid_memory_chunk_list(ms->chunks, ms->block))
  @ } */

typedef struct _memory_slice_list {
  memory_slice*              slice;
  struct _memory_slice_list* next;
} memory_slice_list;

/*@ predicate valid_memory_slice_list(memory_slice_list* msl) {
  @   \valid(msl) && valid_memory_slice(msl->slice)
  @   && (msl->next == \null || valid_memory_slice_list(msl->next))
  @ } */

typedef memory_slice_list* memory_pool;

/*@ predicate valid_memory_pool(memory_pool *mp) {
  @   \valid(mp) && valid_memory_slice_list(*mp)
  @ } */

/*@ behavior zero_size:
  @   assumes s == 0;
  @   assigns \nothing
  @   ensures \result == 0
  @ behavior positive_size:
  @   assumes s > 0;
  @   requires valid_memory_pool(arena);
  @   ensures \result == 0 
  @     || (valid_memory_chunk(\result,s) && used_memory_chunk(*\result));
  @ */
memory_chunk* memory_alloc(memory_pool* arena, unsigned int s) {
  memory_slice_list *msl = *arena;
  memory_chunk_list *mcl;
  memory_slice *ms;
  memory_block *mb;
  memory_chunk *mc;
  unsigned int mb_size;
  //@ ghost unsigned int mcl_offset;
  char *mb_data;
  // guard condition
  if (s == 0) return 0;
  // iterate through memory blocks (or slices)
  /*@ 
    @ loop invariant valid_memory_slice_list(msl)
    @ */
  while (msl != 0) {
    ms = msl->slice;
    mb = ms->block;
    mcl = ms->chunks;
    // does [mb] contain enough free space?
    if (s <= mb->size - mb->next) {
      // allocate a new chunk
      mc = (memory_chunk*)malloc(sizeof(memory_chunk));
      if (mc == 0) return 0;
      mc->offset = mb->next;
      mc->size = s;
      mc->free = false;
      mc->block = mb;
      // update block accordingly
      mb->next += s;
      mb->used += s;
      // add the new chunk to the list
      mcl = (memory_chunk_list*)malloc(sizeof(memory_chunk_list));
      if (mcl == 0) return 0;
      //@ ghost mcl_offset = msl->chunks->offset + msl->chunks->chunk->size;
      //@ ghost mcl->offset = mcl_offset;
      mcl->chunk = mc;
      mcl->next = ms->chunks;
      ms->chunks = mcl;
      return mc;
    }
    // iterate through memory chunks
    /*@ 
      @ loop invariant valid_memory_chunk_list(mcl,mb)
      @ */
    while (mcl != 0) {
      mc = mcl->chunk;
      // is [mc] free and large enough?
      if (mc->free && s <= mc->size) {
        mc->free = false;
        mb->used += mc->size;
        return mc;
      }
      // try next chunk
      mcl = mcl->next;
    }
    msl = msl->next;
  }
  // allocate a new block
  mb_size = (DEFAULT_BLOCK_SIZE < s) ? s : DEFAULT_BLOCK_SIZE;
  mb_data = (char*)malloc(mb_size);
  if (mb_data == 0) return 0;
  mb = (memory_block*)malloc(sizeof(memory_block));
  if (mb == 0) return 0;
  mb->size = mb_size;
  mb->next = s;
  mb->used = s;
  mb->data = mb_data;
  // allocate a new chunk
  mc = (memory_chunk*)malloc(sizeof(memory_chunk));
  if (mc == 0) return 0;
  mc->offset = 0;
  mc->size = s;
  mc->free = false;
  mc->block = mb;
  // allocate a new chunk list
  mcl = (memory_chunk_list*)malloc(sizeof(memory_chunk_list));
  if (mcl == 0) return 0;
  //@ ghost mcl->offset = 0;
  mcl->chunk = mc;
  mcl->next = 0;
  // allocate a new slice
  ms = (memory_slice*)malloc(sizeof(memory_slice));
  if (ms == 0) return 0;
  ms->block = mb;
  ms->chunks = mcl;
  // update the block accordingly
  mb->slice = ms;
  // add the new slice to the list
  msl = (memory_slice_list*)malloc(sizeof(memory_slice_list));
  if (msl == 0) return 0;
  msl->slice = ms;
  msl->next = *arena;
  *arena = msl;
  return mc;
}

/*@ behavior null_chunk:
  @   assumes chunk == \null
  @   assigns \nothing
  @ behavior valid_chunk:
  @   assumes chunk != \null
  @   requires valid_memory_pool(arena) && valid_used_memory_chunk(chunk);
  @   ensures (valid_memory_chunk(chunk) && freed_memory_chunk(chunk)) 
  @     || ! \valid(chunk);
  @ */
void memory_free(memory_pool* arena, memory_chunk* chunk) {
  memory_block *mb = chunk->block;
  memory_slice *ms = mb->slice;
  memory_chunk_list *mcl;
  memory_chunk *mc;
  // is it the last chunk in use in the block?
  if (mb->used == chunk->size) {
    // deallocate all chunks in the block
    mcl = ms->chunks;
    // iterate through memory chunks
    /*@ 
      @ loop invariant valid_memory_chunk_list(mcl,mb)
      @ */
    while (mcl != 0) {
      memory_chunk_list *mcl_next = mcl->next;
      mc = mcl->chunk;
      free(mc);
      free(mcl);
      mcl = mcl_next;
    }
    mb->next = 0;
    mb->used = 0;
    return;
  }
  // mark the chunk as freed
  chunk->free = true;
  // update the block accordingly
  mb->used -= chunk->size;
  return;
}
