
#!/bin/bash

# Script for building the C++ BNFC-based VNNLib parser

set -e  # Exit on any error
set -u  # Exit on undefined variables

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Clean previous builds
clean_build() {
    log_info "Cleaning previous builds..."
    
    # Clean C++ parser
    if [ -d "parsers/cpp/build" ]; then
        rm -rf parsers/cpp/build
        log_info "Removed C++ build directory"
    fi
    
    if [ -d "parsers/cpp/bin" ]; then
        rm -rf parsers/cpp/bin
        log_info "Removed C++ bin directory"
    fi
    
    # Clean generated parser files
    if [ -d "parsers/cpp/src/generated" ]; then
        cd parsers/cpp/src/generated
        rm -f Parser.C Lexer.C Bison.H *.o
        cd ../../../../
        log_info "Cleaned generated parser files"
    fi
    
    # Clean Python builds
    if [ -d "parsers/python/build" ]; then
        rm -rf parsers/python/build
        log_info "Removed Python build directory"
    fi
    
    if [ -d "parsers/python/vnnlib.egg-info" ]; then
        rm -rf parsers/python/vnnlib.egg-info
        log_info "Removed Python egg-info"
    fi
    
    log_success "Build cleanup completed"
}

# Generate BNFC files
generate_bnfc_files() {
    log_info "Generating BNFC files..."
    
    # Check if BNFC is installed
    if ! command -v bnfc >/dev/null 2>&1; then
        log_error "BNFC is not installed. Please install it first."
        exit 1
    fi
    
    # Generate C++ files from the grammar
    bnfc --cpp -o parsers/cpp/src/generated syntax.cf || {
        log_error "BNFC generation failed"
        exit 1
    }
    
    log_success "BNFC files generated successfully"
}

# Build C++ library
build_cpp() {
    log_info "Building C++ parser library..."
    
    # Check C++ dependencies
    local missing_deps=()
    command -v bnfc >/dev/null 2>&1 || missing_deps+=("bnfc")
    command -v make >/dev/null 2>&1 || missing_deps+=("make")
    command -v g++ >/dev/null 2>&1 || missing_deps+=("g++")
    
    if [ ${#missing_deps[@]} -ne 0 ]; then
        log_error "Missing C++ dependencies: ${missing_deps[*]}"
        echo "Please install the missing dependencies and try again."
        exit 1
    fi
    
    cd parsers
    
    # Build using Makefile
    make clean >/dev/null 2>&1 || true  # Don't fail if already clean
    make || {
        log_error "C++ build failed"
        exit 1
    }
    
    cd ..
    log_success "C++ parser library built successfully"
}

# Build Python bindings
build_python() {
    log_info "Building Python bindings..."
    
    # Check Python dependencies
    local missing_deps=()
    command -v python3 >/dev/null 2>&1 || missing_deps+=("python3")
    command -v pip >/dev/null 2>&1 || missing_deps+=("pip")
    
    # Check for Python packages
    if command -v python3 >/dev/null 2>&1; then
        python3 -c "import pybind11" >/dev/null 2>&1 || missing_deps+=("pybind11 (Python package)")
    fi
    
    if [ ${#missing_deps[@]} -ne 0 ]; then
        log_error "Missing Python dependencies: ${missing_deps[*]}"
        echo "Please install the missing dependencies and try again."
        echo "For pybind11, run: pip install pybind11"
        exit 1
    fi
    
    cd parsers/python
    
    # Install in development mode with force reinstall
    python3 -m pip install . --force-reinstall || {
        log_error "Python bindings build failed"
        exit 1
    }
    
    cd ../..
    log_success "Python bindings built and installed"
}

# Run tests
run_tests() {
    if ! python3 -c "import pytest" >/dev/null 2>&1; then
        log_error "pytest is not installed. Please install it first."
        exit 1
    fi

    log_info "Running test suite..."
    
    cd parsers
    
    # Run pytest
    python3 -m pytest -v || {
        log_error "Tests failed"
        exit 1
    }
    
    cd ..
    log_success "All tests passed"
}

# Main build process
main() {
    echo
    log_info "Starting VNNLib C++ Parser Build Process"
    echo "========================================"
    echo
    
    clean_build
    echo
    
    generate_bnfc_files
    echo
    
    build_cpp
    echo
    
    build_python
    echo
    
    log_success "VNNLib C++ parser build completed successfully!"
    echo
    echo "The parser is now ready to use. You can import it with:"
    echo "  import vnnlib"
    echo
    echo "Available functions:"
    echo "  - vnnlib.parse_vnnlib(filename)"
    echo "  - vnnlib.parse_vnnlib_str(content)"
    echo "  - vnnlib.check_query(query)"
    echo
}

# Handle script arguments
case "${1:-}" in
    "clean")
        clean_build
        ;;
    "cpp")
        generate_bnfc_files
        build_cpp
        ;;
    "python")
        build_python
        ;;
    "test")
        run_tests
        ;;
    "help"|"-h"|"--help")
        echo "Usage: $0 [command]"
        echo
        echo "Commands:"
        echo "  (no args)  - Full build process"
        echo "  clean      - Clean build artifacts"
        echo "  cpp        - Build only C++ components"
        echo "  python     - Build only Python bindings"
        echo "  test       - Run test suite"
        echo "  help       - Show this help"
        ;;
    "")
        main
        ;;
    *)
        log_error "Unknown command: $1"
        echo "Use '$0 help' for usage information"
        exit 1
        ;;
esac

