/* A C module in a unikernel: machine.definition declares what this file
   defines; Soma generates machine.soma.h from it, and builds this file for
   Solo5 with the image. Plain C, and assembly where C has none. */
#include <stdlib.h>
#include "machine.soma.h"

struct buffer { size_t n; int64_t *cells; };

soma_handle machine_buffer_new(int64_t n) {
    struct buffer *b = malloc(sizeof *b);
    b->n = (size_t)n;
    b->cells = calloc(b->n ? b->n : 1, sizeof *b->cells);
    return (soma_handle)b;
}

bool machine_buffer_set(soma_handle h, int64_t i, int64_t v) {
    struct buffer *b = (struct buffer *)h;
    if (i < 0 || (size_t)i >= b->n) return false;
    b->cells[i] = v;
    return true;
}

bool machine_buffer_get(soma_handle h, int64_t i, int64_t *out) {
    struct buffer *b = (struct buffer *)h;
    if (i < 0 || (size_t)i >= b->n) return false;
    *out = b->cells[i];
    return true;
}

int64_t machine_buffer_sum(soma_handle h) {
    struct buffer *b = (struct buffer *)h;
    int64_t s = 0;
    for (size_t i = 0; i < b->n; i++) s += b->cells[i];
    return s;
}

/* the ARM generic timer's virtual count, which nothing above assembly
   can read */
int64_t machine_ticks(void) {
    uint64_t t;
    __asm__ __volatile__("isb; mrs %0, cntvct_el0" : "=r"(t));
    return (int64_t)(t >> 1);
}
