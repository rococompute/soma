#include "layout.soma.h"
#if __has_include(<solo5.h>)
#include <solo5.h>
#endif

uint64_t layout_guest_start(void) {
#ifdef SOLO5_HAVE_USER_MEMORY
    struct solo5_user_memory_info info;
    if (solo5_user_memory_acquire("guest", &info) == SOLO5_R_OK) return info.address;
#endif
    return 0;
}
uint64_t layout_guest_size(void) {
#ifdef SOLO5_HAVE_USER_MEMORY
    struct solo5_user_memory_info info;
    if (solo5_user_memory_acquire("guest", &info) == SOLO5_R_OK) return info.size;
#endif
    return 0;
}
uint64_t layout_text_address(void) {
    extern char _stext[];
    return (uintptr_t)_stext;
}
