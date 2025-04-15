#ifndef UTIL_H
#define UTIL_H

#include <stdlib.h>
#include <stdarg.h> 
#include <string.h> 
#include <stdio.h>

void free_safe(void* ptr);

void* malloc_safe(size_t size);

char* strdup_safe(const char* src);

char *format_string(const char *fmt, ...);

char *append_str(char *buffer, size_t *size, size_t *used, const char *fmt, ...);

#endif