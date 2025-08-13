// VNNLibParser_CLI11.cpp
// C++ port of the provided C/argp CLI to CLI11 with the same behavior.
// Subcommands:
//   check [-v|--verbose] [-j|--json] [-o|--output FILE] VNNLIBFILE


#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cerrno>
#include <memory>
#include <string>
#include <iostream>

#include "CLI11.hpp"

#include "VNNLib.h"
#include "TypeChecker.h"
#include "Parser.H"
#include "ParserError.H"
#include "Absyn.H"
#include "Printer.H"


using file_ptr = std::unique_ptr<FILE, int(*)(FILE*)>;


inline file_ptr make_file_ptr(FILE* f) {
    return file_ptr(f, &fclose);
}


int do_check(VNNLibQuery *parse_tree, bool verbose, bool json) {
    if (verbose) {
        std::printf("Running semantic checks...\n\n");
    }

    auto typeChecker = std::make_unique<TypeChecker>();
    
    typeChecker->visitVNNLibQuery(parse_tree);
    
    if (typeChecker->hasErrors()) {
        std::string report = typeChecker->getErrorReport(json);
        
        if (json) {
            std::cout << report << std::endl;
        } else {
            std::cerr << report << std::endl;
        }
        
        return EXIT_FAILURE;
    }
    
    if (verbose) {
        std::printf("Semantic checks completed successfully.\n");
    }
    
    if (json) {
        std::cout << "{\"status\":\"success\",\"errors\":[]}" << std::endl;
    } else {
        std::cout << "No errors found." << std::endl;
    }
    
    return EXIT_SUCCESS;
}


int main(int argc, char** argv) {
    CLI::App app{"VNNLibParser - Parse and validate VNNLIB specifications"};
    app.require_subcommand(1); 

    // Global exit status we can modify from callbacks
    int exit_status = EXIT_SUCCESS;

    bool verbose = false;
    bool json = false;
    std::string output_path;
    std::string spec_file;

    // Add global options
    auto *check = app.add_subcommand("check", "Parse and perform semantic checks on the VNNLIB file");
    check->add_flag("-v,--verbose", verbose, "Produce verbose output");
    check->add_flag("-j,--json", json, "Output in JSON format");
    check->add_option("VNNLIBFILE", spec_file, "Path to the input VNNLIB specification file")
         ->required()
         ->check(CLI::ExistingFile);

    // Check subcommand callback
    check->callback([&]() {
        if (verbose) {
            std::printf("Verbose mode enabled.\n");
            std::printf("Running Check Mode\n");
            std::printf("Spec File: %s\n", spec_file.c_str());
        }

        // 1) Open input file
        file_ptr input = make_file_ptr(std::fopen(spec_file.c_str(), "r"));
        if (!input) {
            std::fprintf(stderr, "Error: Cannot open input file '%s': %s\n", spec_file.c_str(), std::strerror(errno));
            exit_status = EXIT_FAILURE;
            return; // leave callback
        }
        if (verbose) {
            std::printf("File opened successfully: %s\n", spec_file.c_str());
        }

        VNNLibQuery *parse_tree = nullptr;

        try {
            parse_tree = dynamic_cast<VNNLibQuery*>(pQuery(input.get()));
        } catch (const parse_error &e) {
            std::fprintf(stderr, "Parse error: %s\n", e.what());
            exit_status = EXIT_FAILURE;
            return; 
        }

        if (parse_tree == nullptr) {
            std::fprintf(stderr, "Error: Failed to parse VNNLIB file '%s'\n", spec_file.c_str());
            exit_status = EXIT_FAILURE;
            return;
        }
    
        if (verbose) {
            std::printf("Parse tree generated successfully.\n\n");
            std::printf("[Linearized Tree]\n");
            std::string query_str = write_vnnlib_str(parse_tree);
            std::cout << query_str << std::endl;
        }

        // 3) Run semantic checks
        if (do_check(parse_tree, verbose, json) != 0) {
            exit_status = EXIT_FAILURE;
        }
    });

    try {
        app.parse(argc, argv);
    } catch (const CLI::ParseError& e) {
        return app.exit(e);
    }

    return exit_status;
}