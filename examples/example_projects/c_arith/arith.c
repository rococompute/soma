/* A C module: arith.definition declares what this file defines, and Soma
   generates arith.soma.h from it. Plain C, no OCaml. */
#include <stdlib.h>
#include <string.h>
#include "arith.soma.h"

int64_t arith_sum(int64_t a, int64_t b) { return a + b; }

double arith_scale(double x, double by) { return x * by; }

void arith_shout(soma_str s, soma_buf *out) {
    out->ptr = malloc(s.len + 1);
    for (size_t i = 0; i < s.len; i++) {
        uint8_t c = s.ptr[i];
        out->ptr[i] = (c >= 'a' && c <= 'z') ? c - 32 : c;
    }
    out->ptr[s.len] = '!';
    out->len = s.len + 1;
}

bool arith_first_byte(soma_str s, int64_t *out) {
    if (s.len == 0) return false;
    *out = s.ptr[0];
    return true;
}

/* a handle: a pointer Soma keeps and gives back, never looks into */
struct counter { int64_t n; };

soma_handle arith_counter_new(void) {
    struct counter *c = malloc(sizeof *c);
    c->n = 0;
    return (soma_handle)c;
}

int64_t arith_counter_bump(soma_handle h) {
    struct counter *c = (struct counter *)h;
    return ++c->n;
}
