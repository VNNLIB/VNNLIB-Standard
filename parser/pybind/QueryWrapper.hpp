#pragma once

#include "Absyn.h"
#include "VNNLib.h"
#include <string>


class QueryWrapper {
public:
    Query q;

    QueryWrapper(Query q_) {
		this->q = q_;
	}

    std::string to_string() const {
        char* s = write_vnnlib_str(q);
        std::string result(s); // Convert to std::string
        free(s);
        return result;
    }

    ~QueryWrapper() {
        free_query(q);  // Free the Query object
    }

    Query get() const { return q; } // for passing to C functions
};