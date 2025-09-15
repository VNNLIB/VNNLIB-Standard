#pragma once

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
#include <cerrno>
#include <cstring>

#include "Absyn.H"
#include "Parser.H"
#include "TypedBuilder.h"
#include "Printer.H"
#include "ParserError.H"

#include "Error.hpp"

VNNLIB_API std::unique_ptr<TQuery> parse_query(std::string path);
VNNLIB_API std::unique_ptr<TQuery> parse_query_str(std::string content);
VNNLIB_API std::string check_query(std::string content);
VNNLIB_API std::string check_query_str(std::string content);

