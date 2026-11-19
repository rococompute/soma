/* Never replace even an empty live cache directory during donor restoration. */
#define _GNU_SOURCE
#define _DARWIN_C_SOURCE
#include <errno.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#if defined(__linux__)
#include <sys/syscall.h>
#endif
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/unixsupport.h>

CAMLprim value soma_cache_rename_absent(value source, value destination)
{
    CAMLparam2(source, destination);
    int rc;
    caml_unix_check_path(source, "rename absent cache");
    caml_unix_check_path(destination, "rename absent cache");
#if defined(__APPLE__) && defined(RENAME_EXCL)
    rc = renamex_np(String_val(source), String_val(destination), RENAME_EXCL);
#elif defined(__linux__) && defined(SYS_renameat2)
    rc = syscall(SYS_renameat2, AT_FDCWD, String_val(source),
                 AT_FDCWD, String_val(destination), 1 /* RENAME_NOREPLACE */);
#else
    CAMLreturn(Val_false);
#endif
    if (rc == 0) CAMLreturn(Val_true);
    if (errno == EEXIST || errno == ENOTEMPTY || errno == ENOSYS ||
        errno == EINVAL || errno == ENOTSUP) CAMLreturn(Val_false);
    uerror("rename absent cache", destination);
}
