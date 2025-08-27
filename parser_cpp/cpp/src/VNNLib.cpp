#include "VNNLib.h"

// Forward declaration
extern Query* psQuery(const char *str);

std::unique_ptr<TQuery> parse_query(std::string path) {
    FILE *file = fopen(path.c_str(), "r");
    if (!file) {
        std::fprintf(stderr, "Error: Cannot open input file '%s': %s\n", path.c_str(), std::strerror(errno));
        return nullptr;
    }

    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = pQuery(file);
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        fclose(file);
        throw VNNLibException("Parse error: " + std::string(e.what()));
    }
    fclose(file);
    
    if (parse_tree == nullptr) {
        throw VNNLibException("Error: Failed to parse VNNLIB file: " + path);
    }

    TypedBuilder typeChecker;
    auto typed = typeChecker.build(parse_tree);
    if (typeChecker.hasErrors()) {
        throw VNNLibException(typeChecker.getErrorReport());
    }
    return typed;
}

std::unique_ptr<TQuery> parse_query_str(std::string content) {
    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = psQuery(content.c_str());
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        throw VNNLibException("Parse error: " + std::string(e.what()));
    }
    
    if (parse_tree == nullptr) {
        throw VNNLibException("Error: Failed to parse VNNLIB file: " + content);
    }

    TypedBuilder typeChecker;
    auto typed = typeChecker.build(parse_tree);
    if (typeChecker.hasErrors()) {
        throw VNNLibException(typeChecker.getErrorReport());
    }
    return typed;
}

std::string check_query(std::string path) {
    FILE *file = fopen(path.c_str(), "r");
    if (!file) {
        std::fprintf(stderr, "Error: Cannot open input file '%s': %s\n", path.c_str(), std::strerror(errno));
        return nullptr;
    }

    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = pQuery(file);
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        fclose(file);
        throw VNNLibException("Parse error: " + std::string(e.what()));
    }
    fclose(file);
    
    if (parse_tree == nullptr) {
        throw VNNLibException("Error: Failed to parse VNNLIB file: " + path);
    }

    TypedBuilder typeChecker;
    auto typed = typeChecker.build(parse_tree);
    if (typeChecker.hasErrors()) {
        return typeChecker.getErrorReport();
    }
    return "";
}

std::string check_query_str(std::string content) {
    VNNLibQuery *parse_tree = nullptr;
    try {
        Query *query = psQuery(content.c_str());
        parse_tree = dynamic_cast<VNNLibQuery*>(query);
    } catch (const parse_error &e) {
        throw VNNLibException("Parse error: " + std::string(e.what()));
    }
    
    if (parse_tree == nullptr) {
        throw VNNLibException("Error: Failed to parse VNNLIB file: " + content);
    }

    TypedBuilder typeChecker;
    auto typed = typeChecker.build(parse_tree);
    if (typeChecker.hasErrors()) {
        return typeChecker.getErrorReport();
    }
    return "";
}


