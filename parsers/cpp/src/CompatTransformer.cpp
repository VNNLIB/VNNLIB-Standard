#include "CompatTransformer.h"


// --- Forward declarations ---

static LinearArithExpr combineExprs(const TCompare* node);
static void refineBounds(const Box& box, int index, double coeff, double rhs);
static void refineConstraints(Polytope& polytope, int outputSize, const LinearArithExpr& expr);
static std::string boxSignature(const Box& box);
static bool boxIsUnsat(const Box& box);
static int64_t flattenIndex(const std::vector<int64_t>& shape);

// --- Constructor ---

CompatTransformer::CompatTransformer(const TQuery* query) : _query(const_cast<TQuery*>(query)) {
    if (!_query) throw std::runtime_error("CompatTransformer: null TQuery provided");
}

// --- Main transformation method ---

std::vector<SpecCase> CompatTransformer::transform() {
    // Step 1: Extract input and output declarations from the query
    if (_query->networks.size() != 1) {
        throw VNNLibException("CompatTransformer: Only single-network queries are supported");
    }

    const auto& network = _query->networks[0];

    // Find input variable
    for (auto &input: network->inputs) {
        if (inputSymbol == nullptr) {
            inputSymbol = const_cast<SymbolInfo*>(input->symbol.get());
            _inputSize = flattenIndex(inputSymbol->shape);
        }
        else {
            throw VNNLibException("CompatTransformer: Multiple input variables found; only one is supported");
        }
    }

    // Find output variable
    for (auto &output: network->outputs) {
        if (outputSymbol == nullptr) {
            outputSymbol = const_cast<SymbolInfo*>(output->symbol.get());
            _outputSize = flattenIndex(outputSymbol->shape);
        }
        else {
            throw VNNLibException("CompatTransformer: Multiple output variables found; only one is supported");
        }
    }

    // Create common input bounds
    _commonInputBounds.reserve(_inputSize);
    for (int i = 0; i < _inputSize; ++i) {
        _commonInputBounds.emplace_back(-std::numeric_limits<double>::infinity(), std::numeric_limits<double>::infinity());
    }

    // Single pass to collect assertions and disjunctions
    for (const auto& assertion : _query->assertions) {
        TBoolExpr* expr = assertion->cond.get();
        if (dynamic_cast<TCompare*>(expr)) {
            _literals.push_back(dynamic_cast<TCompare*>(expr));
            // Update common bounds/constraints
            parseLiteral(dynamic_cast<TCompare*>(expr), _commonInputBounds, _commonOutputConstraints);
        }
        else {
            DNF dnf = toDNF(expr);
            _disjunctions.push_back(dnf);
        }
    }

    // Generate the reachability cases from the disjunctions
    enumerateCases();
    return _cases;
}

void CompatTransformer::enumerateCases() {
    std::unordered_map<std::string, SpecCase> uniqueCases;
    uniqueCases.reserve(_disjunctions.size() * 2);

    for (const auto& dnf : _disjunctions) {
        // Each clause in the DNF represents a separate input-output case
        for (const auto& clause : dnf) {
            Box clauseBox = _commonInputBounds;
            Polytope clausePoly = _commonOutputConstraints;
            bool clauseUnsat = false;
            
            // Refine the input box and output polytope with each literal in the clause (AND)
            for (const auto& literal : clause) {
                parseLiteral(literal, clauseBox, clausePoly);
                if (boxIsUnsat(clauseBox)) {
                    clauseUnsat = true;
                    break;
                }
            }
            if (clauseUnsat) continue;
            
            // Merge with existing case if input box matches
            std::string signature = boxSignature(clauseBox);
            auto it = uniqueCases.find(signature);
            if (it != uniqueCases.end()) {
                auto& existingCase = it->second;
                existingCase.outputConstraints.push_back(std::move(clausePoly));
            }
            else {
                SpecCase newCase;
                newCase.inputBox = std::move(clauseBox);
                newCase.outputConstraints.push_back(std::move(clausePoly));
                uniqueCases.emplace(std::move(signature), std::move(newCase));
            }
        }
    }

    _cases.clear();
    _cases.reserve(uniqueCases.size());
    for (auto& [_, specCase] : uniqueCases) {
        _cases.push_back(std::move(specCase));
    }
}

void CompatTransformer::parseLiteral(const TCompare* node, Box& inputBounds, Polytope& outputConstraints) {
    LinearArithExpr linearExpr = combineExprs(node);
    const auto& terms = linearExpr.getTerms();
    double constant = linearExpr.getConstant();

    bool isInputConstraint = false;

    if (terms.empty()) {
        return; // Ignore trivial constraints
    }

    // Determine if this is an input or output constraint
    if (terms[0].var->symbol->kind == SymbolKind::Input) {
        isInputConstraint = true;
    } else if (terms[0].var->symbol->kind == SymbolKind::Output) {
        isInputConstraint = false;
    } else {
        throw VNNLibException("CompatTransformer: Constraints must involve either input or output variables");
    }

    if (isInputConstraint) {
        if (terms.size() > 1) {
            throw VNNLibException("CompatTransformer: Input constraints must be simple bounds on individual variables");
        }
        const auto& var = terms[0].var;
        int index = flattenIndex(var->symbol->shape);
        refineBounds(_commonInputBounds, index, terms[0].coeff, -constant);
    }
    else {
        refineConstraints(_commonOutputConstraints, _outputSize, linearExpr);
    }
}

static std::string caseToString(const SpecCase& c) {
    std::ostringstream oss;

    // Print input box
    oss << "Input Box:\n";
    for (size_t i = 0; i < c.inputBox.size(); ++i) {
        const auto& [lower, upper] = c.inputBox[i];
        oss << "  x" << i << " ∈ [" << lower << ", " << upper << "]\n";
    }

    // Print output constraints
    oss << "Output Constraints (" << c.outputConstraints.size() << " polytopes):\n";
    for (size_t p = 0; p < c.outputConstraints.size(); ++p) {
        const Polytope& poly = c.outputConstraints[p];
        oss << "  Polytope " << p << ":\n";
        for (size_t r = 0; r < poly.coeffMatrix.size(); ++r) {
            oss << "    ";
            const auto& coeffs = poly.coeffMatrix[r];
            bool first = true;
            for (size_t j = 0; j < coeffs.size(); ++j) {
                if (coeffs[j] == 0.0) continue;
                if (!first) oss << " + ";
                oss << coeffs[j] << "*y" << j;
                first = false;
            }
            oss << " <= " << poly.rhs[r] << "\n";
        }
    }

    return oss.str();
}

// --- Helper methods ---

static LinearArithExpr combineExprs(const TCompare* node) {
    // Move all terms to the left-hand side
    std::unique_ptr<LinearArithExpr> linearLHS;
    std::unique_ptr<LinearArithExpr> linearRHS;
    try {
        linearLHS = linearize(node->lhs.get());
        linearRHS = linearize(node->rhs.get());
    } catch (const VNNLibException& e) {
        throw VNNLibException(std::string("CompatTransformer: Non-linear expression encountered: ") + e.what());
    }
    linearLHS->subtractLinearExpr(*linearRHS);
    
    // Normalize to <= form
    if (dynamic_cast<const TGreaterEqual*>(node) || dynamic_cast<const TGreaterThan*>(node)) {
        linearLHS->negate();
    } else if (dynamic_cast<const TNotEqual*>(node)) {
        throw VNNLibException("CompatTransformer: '!=' operator is not supported within literals");
    }
    return *linearLHS;
}

static void refineBounds(const Box& box, int index, double coeff, double rhs) {
    auto &[lower, upper] = box[index];
    if (coeff > 0) {
        double upper = rhs / coeff;
        upper = std::min(upper, upper);
    } else if (coeff < 0) {
        double lower = rhs / coeff;
        lower = std::max(lower, lower);
    } else {
        throw VNNLibException("CompatTransformer: Zero coefficient in constraint");
    }
}

static void refineConstraints(Polytope& polytope, int outputSize, LinearArithExpr& expr) {
    double rhs = -expr.getConstant();
    auto& terms = expr.getTerms();

    std::vector<double> coeffs(outputSize, 0.0);
    for (auto& term : terms) {
        if (term.var->symbol->kind != SymbolKind::Output) {
            throw VNNLibException("CompatTransformer: Input-output mixed constraints are not supported");
        }
        int64_t index = flattenIndex(term.var->symbol->shape);
        if (index < 0 || index >= outputSize) {
            throw VNNLibException("CompatTransformer: Output variable index out of bounds");
        }
        coeffs[index] = term.coeff;
    }

    polytope.coeffMatrix.push_back(std::move(coeffs));
    polytope.rhs.push_back(rhs);
}

static int64_t flattenIndex(const std::vector<int64_t>& shape) {
    auto index = 1;
    for (auto dim : shape) {
        index *= dim;
    }
    return index;
}

static bool boxIsUnsat(const Box& box) {
    for (const auto& [lower, upper] : box) {
        if (lower > upper) return true;
    }
    return false;
}

static std::string boxSignature(const Box &box) {
    std::string s;
    s.reserve(box.size() * sizeof(double) * 2);
    for (const auto &p : box) {
        uint64_t hi, lo;
        std::memcpy(&hi, &p.first, sizeof(double));
        std::memcpy(&lo, &p.second, sizeof(double));
        s.append(reinterpret_cast<const char*>(&hi), sizeof(uint64_t));
        s.append(reinterpret_cast<const char*>(&lo), sizeof(uint64_t));
    }
    return s;
}



