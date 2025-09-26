#pragma once

#include <string>
#include <vector>
#include <unordered_map>
#include <limits>
#include <cstring>

#include "TypedAbsyn.h"
#include "DNFConverter.h"
#include "LinearArithExpr.h"
#include "Error.hpp"


// Represents a linear inequality of the form: coeffs * x <= rhs
struct Polytope {
    std::vector<std::vector<double>> coeffMatrix;       // Coefficients of the inequalities (rows: inequalities, cols: variables)
    std::vector<double> rhs;                         // Right-hand side values of the inequalities
};

using Box = std::vector<std::pair<double, double>>;     // A box defined by (lower, upper) pairs for each dimension
using PolyUnion = std::vector<Polytope>;                // A union of polytopes

// A single reachability specification case with input bounds and output constraints
struct SpecCase {
    Box inputBox;                                           // Input bounds as a box
    PolyUnion outputConstraints{};                            // Output constraints as a union of polytopes
};

// Class to transform a typed AST into a simple reachability-style specification
class CompatTransformer {
public: 
    CompatTransformer(const TQuery* query);
    ~CompatTransformer() = default;

    SymbolInfo* inputSymbol = nullptr;                                 // Information about the input variable
    SymbolInfo* outputSymbol = nullptr;                                // Information about the output variable

    std::vector<SpecCase> transform();
    static std::string caseToString(const SpecCase& c);

private:
    TQuery* _query;

    std::unordered_map<int, std::string> _inputVarNames;
    std::unordered_map<int, std::string> _outputVarNames;

    int _inputSize;
    int _outputSize;

    Box _commonInputBounds;
    Polytope _commonOutputConstraints;
    std::vector<SpecCase> _cases;

    std::vector<TCompare*> _literals;
    std::vector<DNF> _disjunctions;

    void parseLiteral(const TCompare* node, Box& inputBounds, Polytope& outputConstraints);
    void enumerateCases();
};