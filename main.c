#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern int our_code_starts_here(int* HEAP) asm("our_code_starts_here");
extern void error() asm("error");
extern int print(int val) asm("print");
extern int equal(int val1, int val2) asm("equal");
extern int* try_gc(int* alloc_ptr, int amount_needed, int* first_frame, int* stack_top) asm("try_gc");
extern int* HEAP_END asm("HEAP_END");
extern int* STACK_BOTTOM asm("STACK_BOTTOM");

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    int* alloc_ptr - the current top of the heap (which we store in ESI), where
                     the next allocation should occur, if possible
    int bytes_needed - the number of bytes of memory we want to allocate
                       (including padding)
    int* cur_frame - the base pointer of the topmost stack frame of our code
                     (i.e., EBP)
    int* cur_stack_top - the stack pointer of the topmost stack frame of our
                         code (i.e., ESP)

  Returns:
    The new top of the heap (i.e. the new value of ESI) after garbage collection.
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/

// Do you trust your new GC?
/*#define DISABLE_GC*/
/*#define DEBUG*/
#define BIG_SIZE 24
#define SMALL_SIZE 16

size_t HEAP_SIZE;
int* STACK_BOTTOM;
int* HEAP;
int* HEAP_END;

int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) {
  fflush(stdout);
  int* new_heap = (int*)calloc(HEAP_SIZE, sizeof(int));
  int* new_heap_end = new_heap + HEAP_SIZE;
  int* old_heap = HEAP;
  int* old_heap_end = HEAP_END;

  int* new_esi = NULL;

#ifdef DEBUG
  printf("Try GC called! bot_stack = %p\n", STACK_BOTTOM);
  printf("---------------BEFORE-----------------\n");
  naive_print_heap(HEAP, SMALL_SIZE);
#endif

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection");
    exit(ERR_OUT_OF_MEMORY);
  }

#ifdef DISABLE_GC
    // This just keeps ESI where it is, and cleans up after the unneeded allocation
    free(new_heap);
    new_heap = NULL;
    new_esi = alloc_ptr;
#else
    // When you're confident in your collector, enable the following lines to trigger your GC
    new_esi = gc(STACK_BOTTOM, cur_frame, cur_stack_top, HEAP, HEAP_END, new_heap);
    HEAP = new_heap;
    HEAP_END = new_heap_end;
    free(old_heap);
#endif

  // Note: strict greater-than is correct here: if new_esi + (bytes_needed / 4) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / 4 > HEAP_SIZE) {
    fprintf(stderr, "Allocation error: needed %d words, but the heap is only %d words",
            bytes_needed / 4, HEAP_SIZE);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_esi + (bytes_needed / 4)) > HEAP_END) {
    fprintf(stderr, "Out of memory: needed %d words, but only %d remain after collection",
            bytes_needed / 4, (HEAP_END - new_esi));
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  else {
#ifdef DEBUG
    printf("---------------AFTER-----------------\n");
    printf("new_esi = %p old_heap = %p\n", new_esi, alloc_ptr);
    naive_print_heap(HEAP, SMALL_SIZE);
#endif
    return new_esi;
  }
}

int main(int argc, char** argv) {
    /*HEAP_SIZE = argc > 1 ? atoi(argv[1]) : 4096;*/
    if(argc > 1) {
      HEAP_SIZE = atoi(argv[1]);
    }
    else {
      HEAP_SIZE = 4096;
    }
    HEAP = (int*)calloc(HEAP_SIZE, sizeof (int));
    HEAP_END = HEAP + HEAP_SIZE;

    int result = our_code_starts_here(HEAP);

    print(result);
#ifdef DEBUG
    naive_print_heap(HEAP, BIG_SIZE);
#endif
    return 0;
}

int equal(int a, int b)
{
    if (a == b)
        return BOOL_TRUE;

    if (((a & BIT3_MASK) != 0x1) || ((b & BIT3_MASK) != 0x1))
        return BOOL_FALSE;

    const int* tup_a = (int*)(a - 1);
    const int* tup_b = (int*)(b - 1);

    for (size_t i = 0; i <= tup_a[0]; ++i)
        if (equal(tup_a[i], tup_b[i]) == BOOL_FALSE)
            return BOOL_FALSE;

    return BOOL_TRUE;
}

int tupleCounter = 0;
void printHelp(FILE *out, int val) {
  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & BIT3_MASK) == FUNC_TAG) {
    fprintf(out, "<function>");
  }
  else if ((val & BIT3_MASK) != 0) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %p>", (int)(*addr & 0x7FFFFFFE));
      /*return;*/
    }
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0];
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len;
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

int print(int val) {
  printHelp(stdout, val);
  printf("\n");
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: integer overflow\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get\n");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "Error: get expected numer for index\n");
    break;
  case ERR_NOT_LAMBDA:
    fprintf(stderr, "Error: application expected a lambda/function\n");
    break;
  case ERR_WRONG_ARITY:
    fprintf(stderr, "Error: wrong arity for lambda/function\n");
    break;
  default:
    fprintf(stderr, "Error: unknown error code: %d\n", i);
  }
#ifdef DEBUG
  naive_print_heap(HEAP, BIG_SIZE);
#endif
  exit(i);
}

