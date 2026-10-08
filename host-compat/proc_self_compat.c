/* Host compatibility only: Lean's numeric PID and this host's /proc mount use
 * different PID namespaces. Read the permitted path for this executable instead.
 * This changes no Lean parsing, elaboration, axioms, or proof-checking behavior.
 */
#include <unistd.h>
#include <limits.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    char own_path[64];
    snprintf(own_path, sizeof(own_path), "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, own_path) == 0 ? "/proc/self/exe" : path, buf, size);
}
