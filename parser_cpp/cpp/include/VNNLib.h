#pragma once

#ifndef VNNLIB_H
#define VNNLIB_H

#include <cstdlib>

#if defined(_WIN32) || defined(__CYGWIN__)
  #define VNNLIB_API __declspec(dllexport)
#else
  #define VNNLIB_API __attribute__((visibility("default")))
#endif

#include <string>
#include <vector>
#include <unordered_map>
#include <memory>

#include "Absyn.H"
#include "Parser.H"
#include "TypeChecker.h"
#include "Printer.H"
#include "ParserError.H"

VNNLIB_API VNNLibQuery *parse_vnnlib(const char* path);
VNNLIB_API VNNLibQuery *parse_vnnlib_str(const char* str);

VNNLIB_API std::string write_vnnlib_str(VNNLibQuery *q);

VNNLIB_API int check_query(VNNLibQuery *q, int json);


#endif

