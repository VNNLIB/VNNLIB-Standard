#include "DNFConverter.h"
#include <stdexcept>

// root-level function to perform DNF conversion
DNF toDNF(const TBoolExpr* node) {
    return dnfOf(node); 
}

DNF dnfOf(const TBoolExpr* node) {
    if (const TAnd* a = dynamic_cast<const TAnd*>(node)) {
        return dnfAnd(a->args);
    }
    else if (const TOr* o = dynamic_cast<const TOr*>(node)) {
        return dnfOr(o->args);
    }
    else if (const TCompare* c = dynamic_cast<const TCompare*>(node)) {
        return DNF{ Clause{c} };
    }
    else {
        throw std::runtime_error("Unsupported TBoolExpr node type in DNF conversion: " + node->toString());
    }
}

DNF dnfOr(const std::vector<std::unique_ptr<TBoolExpr>>& args) {
    DNF out;
    for (const auto& clause : args) {
        if (!clause) continue;
        DNF part = dnfOf(clause.get());                     // Recursively get DNF of the current part
        out.insert(out.end(), part.begin(), part.end());    // Append new part to the current DNF
    }
    return out;
}

DNF dnfAnd(const std::vector<std::unique_ptr<TBoolExpr>>& args) {
    // Start with single empty clause
    DNF out = DNF{ Clause{} };

    for (const auto& clause : args) {
        if (!clause) continue;
        DNF part = dnfOf(clause.get());     // Rescursively get DNF of the current part
        out = distrib(out, part);           // Distribute current DNF with new part
    }
    return out;
}

DNF distrib(const DNF& left, const DNF& right) {
    if (left.empty() || right.empty()) return DNF{};
    DNF out;
    out.reserve(left.size() * right.size());
    for (const auto& conj : left) {
        for (const auto& disj : right) {
            Clause merged;
            merged.reserve(conj.size() + disj.size());
            merged.insert(merged.end(), conj.begin(), conj.end());
            merged.insert(merged.end(), disj.begin(), disj.end());
            out.push_back(std::move(merged));
        }
    }
    return out;
}