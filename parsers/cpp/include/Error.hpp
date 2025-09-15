#pragma once

#include <exception>
#include <string>

class VNNLibException : public std::exception {
private:
    std::string message_;
public:
    VNNLibException(const std::string &message) : message_(message) {}
    const char* what() const noexcept override {
        return message_.c_str();
    }
};