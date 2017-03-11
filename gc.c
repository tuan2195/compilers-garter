#include <stdio.h>
#include "gc.h"

void naive_print_heap(int* heap, int size) {
  for(int i = 0; i < size; ++i)
    printf("  %p: %p (%d)\n", (heap + i), (int*)(*(heap + i)), *(heap + i));
}

// Implement the functions below

void smarter_print_heap(int* from_start, int* from_end, int* to_start, int* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
}

/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location
 */
int* copy_if_needed(int* garter_val_addr, int* heap_top) {
    int val = *garter_val_addr;
    /*printf("copy: addr = %p val = %x top = %p\n", garter_val_addr, val, heap_top);*/
    fflush(stdout);

    if(((val & NUM_TAG_MASK) == 0) || (val == BOOL_TRUE) || (val == BOOL_FALSE))
    {
        return heap_top;
    }
    else if ((val & TUPLE_TAG_MASK) == FUNC_TAG_MASK)
    {
        // Function
        return heap_top;
    }
    else if ((val & TUPLE_TAG_MASK) != 0) // Tuple
    {
        int* addr = (int*)(val-1);
        int size = addr[0];
        size += (size % 2) ? 1 : 2; // Padding
        int* old_top = heap_top;
        for(int i = 0; i < size; ++i)
        {
            heap_top[i] = addr[i];
        }
        *garter_val_addr = (int*)((void*)heap_top + 0x1); // Fucking pointer arithmetic
        /*printf("Old val = %p new val = %p\n", val, *garter_val_addr);*/
        fflush(stdout);
        heap_top += size;
        for(int i = 0; i < size; ++i)
        {
            heap_top = copy_if_needed(&old_top[i], heap_top);
        }
    }
    else
    {
      /*fprintf(stdout, "Unknown value: %#010x", val);*/
    }

    // no-op for now
    return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
int* gc(int* bottom_frame, int* top_frame, int* top_stack, int* from_start, int* from_end, int* to_start) {
  /*printf("gc bot = %p top_frame = %p top_stack = %p from_start = %p from_end = %p to_start = %p\n",*/
          /*bottom_frame, top_frame, top_stack, from_start, from_end, to_start);*/
  fflush(stdout);

  for (int* cur_word = bottom_frame; cur_word >= top_stack; --cur_word)
  {
    /*printf("loop body: cur_word = %p\n", cur_word);*/
    /*fflush(stdout);*/
    to_start = copy_if_needed(cur_word, to_start);
  }
  /*if (top_frame < bottom_frame)*/
    /*to_start = gc(bottom_frame,*/
                  /*(int*)(*top_frame), // [top_frame] points to the saved EBP, which is the next stack frame*/
                  /*top_frame + 2,      // [top_frame+4] points to the return address*/
                                      /*// so [top_frame+8] is the next frame's stack-top*/
                  /*from_start,*/
                  /*from_end,*/
                  /*to_start); // to_start has been changed to include any newly copied data*/
  // after copying the remaining stack frames, return the new allocation starting point
  return to_start;
}

