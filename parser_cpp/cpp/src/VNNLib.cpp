#include "VNNLib.h"
#include "Parser.H"
#include "ParserError.H"
#include "TypeChecker.h"
#include <memory>
#include <cerrno>
#include <cstring>

// Forward declaration for the string parser function
extern Query* psQuery(const char *str);

VNNLibQuery *parse_vnnlib(const char* path) {
    FILE *file = fopen(path, "r");
    if (!file) {
        std::fprintf(stderr, "Error: Cannot open input file '%s': %s\n", path, std::strerror(errno));
        return nullptr;
    }

    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = pQuery(file);
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        std::fprintf(stderr, "Parse error: %s\n", e.what());
        fclose(file);
        return nullptr;
    }
    
    fclose(file);
    
    if (parse_tree == nullptr) {
        std::fprintf(stderr, "Error: Failed to parse VNNLIB file '%s'\n", path);
        return nullptr;
    }
    
    return parse_tree;
}

VNNLibQuery *parse_vnnlib_str(const char* str) {
    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = psQuery(str);
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        std::fprintf(stderr, "Parse error: %s\n", e.what());
        return nullptr;
    }
    
    if (parse_tree == nullptr) {
        std::fprintf(stderr, "Error: Failed to parse VNNLIB string\n");
        return nullptr;
    }
    
    return parse_tree;
} 

std::string write_vnnlib_str(VNNLibQuery *q) {
    auto printer = std::make_unique<ShowAbsyn>();
    char *output = printer->show(dynamic_cast<Visitable*>(q));
    std::string result;

    if (output) {
        result = output;
        delete[] output;
    }
    return result;
}

std::string check_query(VNNLibQuery *q) {
    if (q == nullptr) {
        std::cerr << "Error: Null query provided" << std::endl;
        return "";
    }

    auto typeChecker = std::make_unique<TypeChecker>();
    typeChecker->visitVNNLibQuery(q);
    
    if (typeChecker->hasErrors()) {
        std::string report = typeChecker->getErrorReport();
        return report;
    }

    return "";
}


