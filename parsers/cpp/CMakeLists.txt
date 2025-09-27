cmake_minimum_required(VERSION 3.16)
project(VNNLib LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# ------------------------------------------------------------
# Find required tools
# ------------------------------------------------------------

find_program(BNFC_EXECUTABLE bnfc REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# ------------------------------------------------------------
# Compiler flags
# ------------------------------------------------------------

if(MSVC)
    add_compile_options(/W4 /permissive- /EHsc)
else()
    add_compile_options(-Wall -Wextra -g -Wno-unused-parameter -Wno-unused-function)
endif()

# ------------------------------------------------------------
# Directories
# ------------------------------------------------------------

set(SRC_DIR ${CMAKE_SOURCE_DIR}/src)
set(GENERATED_DIR ${SRC_DIR}/generated)
set(INCLUDE_DIR ${CMAKE_SOURCE_DIR}/include)

# Output directories
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)

# Includes
include_directories(
    ${GENERATED_DIR}
    ${INCLUDE_DIR}
    ${INCLUDE_DIR}/util
)

# ------------------------------------------------------------
# BNFC generation
# ------------------------------------------------------------

set(BNFC_INPUT ${CMAKE_SOURCE_DIR}/../../syntax.cf)

add_custom_command(
    OUTPUT
        ${GENERATED_DIR}/Absyn.C
        ${GENERATED_DIR}/Absyn.H
        ${GENERATED_DIR}/Printer.C
        ${GENERATED_DIR}/Printer.H
        ${GENERATED_DIR}/Buffer.C
        ${GENERATED_DIR}/Buffer.H
        ${GENERATED_DIR}/syntax.y
        ${GENERATED_DIR}/syntax.l
        ${GENERATED_DIR}/Parser.H
        ${GENERATED_DIR}/ParserError.H
        ${GENERATED_DIR}/Skeleton.C
        ${GENERATED_DIR}/Skeleton.H
        ${GENERATED_DIR}/Test.C
    COMMAND ${CMAKE_COMMAND} -E make_directory ${GENERATED_DIR}
    COMMAND ${BNFC_EXECUTABLE} --cpp -o ${GENERATED_DIR} ${BNFC_INPUT}
    DEPENDS ${BNFC_INPUT}
    COMMENT "Running BNFC on ${BNFC_INPUT}"
    VERBATIM
)

add_custom_target(BNFCGen
    DEPENDS
        ${GENERATED_DIR}/Absyn.C
        ${GENERATED_DIR}/Absyn.H
        ${GENERATED_DIR}/Printer.C
        ${GENERATED_DIR}/Printer.H
        ${GENERATED_DIR}/Buffer.C
        ${GENERATED_DIR}/Buffer.H
        ${GENERATED_DIR}/syntax.y
        ${GENERATED_DIR}/syntax.l
        ${GENERATED_DIR}/Parser.H
        ${GENERATED_DIR}/ParserError.H
        ${GENERATED_DIR}/Skeleton.C
        ${GENERATED_DIR}/Skeleton.H
        ${GENERATED_DIR}/Test.C
)

# ------------------------------------------------------------
# Bison / Flex
# ------------------------------------------------------------

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# Custom commands for Bison and Flex (similar to Makefile approach)
add_custom_command(
    OUTPUT ${GENERATED_DIR}/Parser.C ${GENERATED_DIR}/Bison.H
    COMMAND ${BISON_EXECUTABLE} -t -psyntax_ -d ${GENERATED_DIR}/syntax.y -o ${GENERATED_DIR}/Parser.C
    DEPENDS ${GENERATED_DIR}/syntax.y BNFCGen
    WORKING_DIRECTORY ${GENERATED_DIR}
    COMMENT "Running Bison on syntax.y"
    VERBATIM
)

add_custom_command(
    OUTPUT ${GENERATED_DIR}/Lexer.C
    COMMAND ${FLEX_EXECUTABLE} -Psyntax_ -o${GENERATED_DIR}/Lexer.C ${GENERATED_DIR}/syntax.l
    DEPENDS ${GENERATED_DIR}/syntax.l ${GENERATED_DIR}/Bison.H BNFCGen
    WORKING_DIRECTORY ${GENERATED_DIR}
    COMMENT "Running Flex on syntax.l"
    VERBATIM
)

# Create targets for parser generation
add_custom_target(ParserGen
    DEPENDS ${GENERATED_DIR}/Parser.C ${GENERATED_DIR}/Lexer.C ${GENERATED_DIR}/Bison.H
)

# ------------------------------------------------------------
# Sources
# ------------------------------------------------------------

set(MAIN_SRCS
    ${SRC_DIR}/VNNLib.cpp
    ${SRC_DIR}/TypeChecker.cpp
    ${SRC_DIR}/TypedAbsyn.cpp
    ${SRC_DIR}/TypedBuilder.cpp
    ${SRC_DIR}/LinearArithExpr.cpp
    ${SRC_DIR}/CompatTransformer.cpp
    ${SRC_DIR}/DNFConverter.cpp
)

set(PARSER_MAIN
    ${SRC_DIR}/VNNLibParser.cpp
)

set(GENERATED_SRCS
    ${GENERATED_DIR}/Absyn.C
    ${GENERATED_DIR}/Printer.C
    ${GENERATED_DIR}/Buffer.C
    ${GENERATED_DIR}/Parser.C
    ${GENERATED_DIR}/Lexer.C
)

# Ensure uppercase .C files are treated as C++
set_source_files_properties(${GENERATED_SRCS} PROPERTIES LANGUAGE CXX)

# Add specific compiler flags for generated files (suppress warnings)
set_source_files_properties(${GENERATED_SRCS} PROPERTIES COMPILE_FLAGS "-Wno-sign-conversion")

# ------------------------------------------------------------
# Library
# ------------------------------------------------------------

add_library(VNNLib SHARED
    ${MAIN_SRCS}
    ${GENERATED_SRCS}
)

# Ensure parser generation happens before building library
add_dependencies(VNNLib BNFCGen ParserGen)

if(UNIX)
    target_link_libraries(VNNLib m)
endif()

# ------------------------------------------------------------
# Executable
# ------------------------------------------------------------

add_executable(VNNLibParser
    ${MAIN_SRCS}
    ${PARSER_MAIN}
    ${GENERATED_SRCS}
)

# Ensure parser generation happens before building executable
add_dependencies(VNNLibParser BNFCGen ParserGen)

if(UNIX)
    target_link_libraries(VNNLibParser m)
endif()

# Add clean target for generated files
add_custom_target(clean-generated
    COMMAND ${CMAKE_COMMAND} -E remove_directory ${GENERATED_DIR}
    COMMENT "Cleaning generated parser files"
)
