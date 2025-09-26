#pragma once

#include <vector>
#include <string>
#include <memory>
#include <iostream>
#include <iomanip>
#include <unordered_map>
#include "TypedAbsyn.h"
#include "Error.hpp"

/**
 * @brief Represents a linear arithmetic expression of the form:
 *        c0 + c1*x1 + c2*x2 + ... + cn*xn
 * 
 */
class LinearArithExpr {
public:
    struct Term {
        double coeff;           // Coefficient of the variable
        std::string varName;    // Variable name (e.g., "X[0]")
        const TVarExpr* var;     // Pointer to the variable expression

        Term() : coeff(0.0), var(nullptr) {}
        Term(double c, const std::string& name, const TVarExpr* v) : coeff(c), varName(name), var(v) {}
    };

private:
    std::unordered_map<std::string, Term> termMap_;     // Map from variable name to Term
    double constant_;                                   // Constant term

public:
    // Constructors
    LinearArithExpr();
    LinearArithExpr(double constant);
    LinearArithExpr(const LinearArithExpr& other);
    LinearArithExpr& operator=(const LinearArithExpr& other);
    
    // Destructor
    virtual ~LinearArithExpr();

    // Accessors
    std::vector<Term> getTerms() const { 
        std::vector<Term> terms;
        terms.reserve(getNumTerms());
        for (const auto& pair : termMap_) {
            terms.push_back(pair.second);
        }
        return terms;
    }
    double getConstant() const { return constant_; }
    size_t getNumTerms() const { return termMap_.size(); }

    // Mutators
    void setConstant(double constant) { constant_ = constant; }
    void addTerm(double coeff, const TVarExpr* var);
    void addConstant(double value) { constant_ += value; }
    
    // Operations
    void negate();
    void multiply(double scalar);
    void addLinearExpr(const LinearArithExpr& other);
    void subtractLinearExpr(const LinearArithExpr& other);
    
    // Utility functions
    std::string toString() const;
    void clear();
    bool isEmpty() const;
    
    // Find coefficient of a variable (returns 0 if not found)
    double getCoefficient(const std::string& varName) const;
    
    // Remove terms with zero coefficients
    void simplify();
};

/**
 * @brief Linearizes a TArithExpr into a LinearArithExpr.
 * @param arithExpr The TArithExpr to linearize.
 * @return A unique_ptr to LinearArithExpr representing the linearized form.
 * @throws VNNLibException if the expression is non-linear.
 */
std::unique_ptr<LinearArithExpr> linearize(const TArithExpr* arithExpr);
