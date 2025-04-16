#ifndef VNNLIB_H
#define VNNLIB_H

#ifdef __cplusplus
extern "C" {
#endif

#if defined(_WIN32) || defined(__CYGWIN__)
  #define VNNLIB_API __declspec(dllexport)
#else
  #define VNNLIB_API __attribute__((visibility("default")))
#endif


#include "Absyn.h"
#include "Parser.h"
#include "SemanticChecker.h"
#include "Printer.h"

VNNLIB_API Query parse_vnnlib(const char* path);
VNNLIB_API Query parse_vnnlib_str(const char* str);
VNNLIB_API void free_query(Query q);

VNNLIB_API int write_vnnlib(const Query q, const char* path);
VNNLIB_API char* write_vnnlib_str(const Query q);

VNNLIB_API char* check_query(const Query q, int json);


#ifdef __cplusplus
}
#endif

#endif