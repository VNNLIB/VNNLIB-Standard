#include "LinearArithExpr.h"

// Constructors and Destructor
LinearArithExpr::LinearArithExpr() : constant_(0.0) {}

LinearArithExpr::LinearArithExpr(double constant) : constant_(constant) {}

LinearArithExpr::LinearArithExpr(const LinearArithExpr& other) 
    : termMap_(other.termMap_), constant_(other.constant_) {}

LinearArithExpr& LinearArithExpr::operator=(const LinearArithExpr& other) {
    if (this != &other) {
        termMap_ = other.termMap_;
        constant_ = other.constant_;
    }
    return *this;
}

LinearArithExpr::~LinearArithExpr() {}

// Member functions
void LinearArithExpr::addTerm(double coeff, const TVarExpr* var) {
    if (std::abs(coeff) < 1e-9) {
        return; 
    }
    
    // Create unique variable identifier including name and indices
    std::string varName = var->symbol->name;
    if (!var->indices.empty()) {
        varName += "[";
        for (size_t i = 0; i < var->indices.size(); ++i) {
            if (i > 0) varName += ",";
            varName += std::to_string(var->indices[i]);
        }
        varName += "]";
    }
    
    auto it = termMap_.find(varName);
    if (it != termMap_.end()) {
        // Update existing term coefficient
        it->second.coeff += coeff;
        if (std::abs(it->second.coeff) < 1e-9) {
            // Remove term if coefficient becomes zero
            termMap_.erase(it);
        }
    } else {            // New variable, add new term
        termMap_[varName] = Term(coeff, varName, var);
    }
}

void LinearArithExpr::negate() {
    constant_ = -constant_;
    for (auto& pair : termMap_) {
        pair.second.coeff = -pair.second.coeff;
    }
}

void LinearArithExpr::multiply(double scalar) {
    constant_ *= scalar;
    for (auto& pair : termMap_) {
        pair.second.coeff *= scalar;
    }
}

void LinearArithExpr::addLinearExpr(const LinearArithExpr& other) {
    constant_ += other.constant_;
    for (const auto& pair : other.termMap_) {
        addTerm(pair.second.coeff, pair.second.var);
    }
}

void LinearArithExpr::subtractLinearExpr(const LinearArithExpr& other) {
    constant_ -= other.constant_;
    for (const auto& pair : other.termMap_) {
        addTerm(-pair.second.coeff, pair.second.var);
    }
}

std::string LinearArithExpr::toString() const {
    std::ostringstream oss;
    bool firstTerm = true;

    // Handle constant term first if it's non-zero or if there are no variable terms
    if (std::abs(constant_) > 1e-9 || termMap_.empty()) {
        oss << std::fixed << std::setprecision(4) << constant_;
        firstTerm = false;
    }
    // Handle variable terms
    for (const auto& pair : termMap_) {
        if (std::abs(pair.second.coeff) < 1e-9) {
            continue; // Skip small coefficients
        }
        // Determine sign and operator
        if (firstTerm) {
            if (pair.second.coeff < 0) oss << "-";
        } else {
            if (pair.second.coeff < 0) {
                oss << " - ";
            } else {
                oss << " + ";
            }
        }
        double absCoeff = std::abs(pair.second.coeff);
        // Print coefficient only if it's not 1.0
        if (std::abs(absCoeff - 1.0) > 1e-9) {
            oss << std::fixed << std::setprecision(4) << absCoeff << " * ";
        }
        oss << pair.second.var->toString();
        if (firstTerm) firstTerm = false;   
    }
    // If nothing was printed, represent as "0"
    if (firstTerm) {
        oss << "0";
    }
    return oss.str();
}

void LinearArithExpr::clear() {
    termMap_.clear();
    constant_ = 0.0;
}

bool LinearArithExpr::isEmpty() const {
    return termMap_.empty() && std::abs(constant_) < 1e-9;
}

double LinearArithExpr::getCoefficient(const std::string& varName) const {
    auto it = termMap_.find(varName);
    return (it != termMap_.end()) ? it->second.coeff : 0.0;
}

void LinearArithExpr::simplify() {
    // Remove terms with zero coefficients
    for (auto it = termMap_.begin(); it != termMap_.end();) {
        if (std::abs(it->second.coeff) < 1e-9) {
            it = termMap_.erase(it);
        } else {
            ++it;
        }
    }
}

// Helper function to extract numeric value from TLiteral
double extractNumericValue(const TLiteral* literal) {
    // Check if it's a TFloat or TInt
    if (const auto* floatLit = dynamic_cast<const TFloat*>(literal)) {
        return floatLit->value;
    } else if (const auto* intLit = dynamic_cast<const TInt*>(literal)) {
        return static_cast<double>(intLit->value);
    } else {
        throw VNNLibException("Unsupported literal type");
    }
}

// Main linearization function
std::unique_ptr<LinearArithExpr> linearize(const TArithExpr* arithExpr) {
    auto result = std::make_unique<LinearArithExpr>();

    // --- Base Cases ---

    if (const auto* varExpr = dynamic_cast<const TVarExpr*>(arithExpr)) {
        // Single variable with coefficient 1.0
        result->addTerm(1.0, varExpr);
        
    } else if (const auto* literal = dynamic_cast<const TLiteral*>(arithExpr)) {
        // Constant value
        double value = extractNumericValue(literal);
        result->setConstant(value);

    // --- Recursive Cases ---
        
    } else if (const auto* negateExpr = dynamic_cast<const TNegate*>(arithExpr)) {
        // Negation: linearize sub-expression and negate
        auto subResult = linearize(negateExpr->expr.get());
        *result = *subResult;
        result->negate();
        
    } else if (const auto* plusExpr = dynamic_cast<const TPlus*>(arithExpr)) {        
        for (const auto& operand : plusExpr->args) {
            auto operandResult = linearize(operand.get());
            result->addLinearExpr(*operandResult);
        }

    } else if (const auto* minusExpr = dynamic_cast<const TMinus*>(arithExpr)) {
        // Subtraction: first operand minus sum of remaining operands
        auto firstResult = linearize(minusExpr->head.get());
        *result = *firstResult;
        
        for (const auto& operand : minusExpr->rest) {
            auto operandResult = linearize(operand.get());
            result->subtractLinearExpr(*operandResult);
        }

    } else if (const auto* multiplyExpr = dynamic_cast<const TMultiply*>(arithExpr)) {
        std::vector<std::unique_ptr<LinearArithExpr>> operands;
        for (const auto& operand : multiplyExpr->args) {
            operands.push_back(linearize(operand.get()));
        }
        
        // Check for linearity: at most one operand can have variables
        LinearArithExpr* varOperand = nullptr;
        double constantProduct = 1.0;
        
        for (const auto& operand : operands) {
            if (operand->getNumTerms() > 0) {
                if (varOperand != nullptr) {
                    throw VNNLibException("Non-linear expression: multiplication of variables detected");
                }
                varOperand = operand.get();
            } else {
                constantProduct *= operand->getConstant();
            }
        }
        
        if (varOperand) {
            // Copy variable operand and multiply by constant product
            *result = *varOperand;
            result->multiply(constantProduct);
        } else {
            // All operands are constants
            result->setConstant(constantProduct);
        }  

    } else {
        throw VNNLibException("Unsupported TArithExpr type for linearization");
    }

    result->simplify();
    return result;
}
