#pragma once

#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <memory>

#include "TypedAbsyn.h"
#include "Absyn.H"

using Literal = const TCompare*;                // A Boolean literal is a comparison (e.g., x <= 5)
using Clause = std::vector<Literal>;            // A clause is a conjunction of literals 
using DNF    = std::vector<Clause>;             // DNF is a disjunction of clauses

DNF toDNF(const TBoolExpr* node);
DNF dnfOf(const TBoolExpr* node);
DNF dnfOr(const std::vector<std::unique_ptr<TBoolExpr>>& args);
DNF dnfAnd(const std::vector<std::unique_ptr<TBoolExpr>>& args);
DNF distrib(const DNF& left, const DNF& right);


