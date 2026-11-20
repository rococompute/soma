#include "pattern.soma.h"

/* each byte of the buffer, in place: seed, seed + 1, ... */
bool pattern_fill(soma_bytes b, int64_t seed) {
    for (size_t i = 0; i < b.len; i++)
        b.ptr[i] = (uint8_t)(seed + (int64_t)i);
    return b.len > 0;
}
