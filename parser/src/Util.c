/*** This file contains functions for safe memory allocation, string duplication, 
 * and formatted string appending. 
*/


#include "Util.h"


void free_safe(void* ptr) {
    if (ptr) free(ptr);
}


void* malloc_safe(size_t size) {
    void* ptr = malloc(size);
    if (!ptr) {
        perror("Failed to allocate memory");
        exit(EXIT_FAILURE);
    }
    return ptr;
}


char* strdup_safe(const char* src) {
    if (!src) return NULL;
    size_t len = strlen(src);
    char* dst = (char *)malloc_safe(len + 1);
    if (dst) strcpy(dst, src);
    return dst;
}


// Returns a formatted string. The caller is responsible for freeing the returned string.
char *format_string(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);

    // Calculate required length
    int needed = vsnprintf(NULL, 0, fmt, args);
    va_end(args);

    // Formatting error
    if (needed < 0) {
        va_end(args);
        return NULL; 
    }

    // Allocate buffer
    char *buffer = (char *)malloc_safe(needed + 1);

    // Format string
    va_start(args, fmt);
    vsnprintf(buffer, needed + 1, fmt, args);
    va_end(args);

    return buffer;
}


// Appends a formatted string to a buffer, resizing it if necessary.
// The caller is responsible for freeing the buffer.
char *append_str(char *buffer, size_t *size, size_t *used, const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);

    // Calculate required length
    int needed = vsnprintf(NULL, 0, fmt, args);
    va_end(args);

    if (*used + needed + 1 >= *size) {
        *size = (*used + needed + 1) * 2; // Grow size of buffer
        buffer = (char *)realloc(buffer, *size);
        if (!buffer) {
            perror("Failed to reallocate memory for buffer");
            exit(EXIT_FAILURE);
        }
    }

    va_start(args, fmt);
    vsnprintf(buffer + *used, *size - *used, fmt, args);
    va_end(args);

    *used += needed;
    return buffer;
}


