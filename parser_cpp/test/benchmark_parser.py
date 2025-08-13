#!/usr/bin/env python3
"""Simple benchmarking script for VNNLib parsing performance."""

import sys
import os
import time
import argparse
from pathlib import Path

# Add the parser path to import vnnlib
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'parser_cpp', 'python'))

try:
    import vnnlib
except ImportError:
    print("Error: Could not import vnnlib. Make sure the parser is built and installed.")
    sys.exit(1)

def benchmark_parse(file_path, iterations=1):
    """Benchmark parsing a VNNLib file."""
    if not os.path.exists(file_path):
        print(f"Error: File '{file_path}' not found.")
        return None
    
    file_size = os.path.getsize(file_path)
    
    print(f"Benchmarking: {file_path}")
    print(f"File size: {file_size:,} bytes")
    print(f"Iterations: {iterations}")
    print("-" * 50)
    
    times = []
    
    for i in range(iterations):
        start_time = time.perf_counter()
        
        try:
            query = vnnlib.parse_vnnlib(file_path)
            end_time = time.perf_counter()
            
            parse_time = end_time - start_time
            times.append(parse_time)
            
            if iterations == 1:
                # Show details for single run
                print(f"Parse time: {parse_time:.6f} seconds")
                print(f"Networks: {len(query.networks)}")
                print(f"Assertions: {len(query.assertions)}")
            else:
                # Show progress for multiple runs
                print(f"Run {i+1:3d}: {parse_time:.6f}s")
                
        except Exception as e:
            print(f"Error parsing file: {e}")
            return None
    
    if iterations > 1:
        # Calculate statistics
        min_time = min(times)
        max_time = max(times)
        avg_time = sum(times) / len(times)
        
        print("-" * 50)
        print(f"Statistics ({iterations} runs):")
        print(f"  Min time:     {min_time:.6f}s")
        print(f"  Max time:     {max_time:.6f}s")
        print(f"  Average time: {avg_time:.6f}s")
        print(f"  Throughput:   {file_size / avg_time / 1024:.2f} KB/s")
    else:
        print(f"Throughput: {file_size / times[0] / 1024:.2f} KB/s")
    
    return times

def main():
    parser = argparse.ArgumentParser(description="Benchmark VNNLib parsing performance")
    parser.add_argument("file", help="VNNLib file to parse")
    parser.add_argument("-n", "--iterations", type=int, default=1, 
                       help="Number of iterations to run (default: 1)")
    parser.add_argument("-a", "--all", action="store_true",
                       help="Benchmark all test files in test/ directory")
    
    args = parser.parse_args()
    
    if args.all:
        # Benchmark all test files
        test_dir = Path("test")
        if not test_dir.exists():
            print("Error: test/ directory not found.")
            return
        
        vnnlib_files = list(test_dir.glob("*.vnnlib"))
        if not vnnlib_files:
            print("No .vnnlib files found in test/ directory.")
            return
        
        print(f"Benchmarking {len(vnnlib_files)} test files...")
        print("=" * 60)
        
        results = {}
        for file_path in sorted(vnnlib_files):
            print()
            times = benchmark_parse(str(file_path), args.iterations)
            if times:
                avg_time = sum(times) / len(times)
                results[file_path.name] = avg_time
        
        # Summary
        if results:
            print("\n" + "=" * 60)
            print("SUMMARY (average times):")
            print("-" * 60)
            for filename, avg_time in sorted(results.items(), key=lambda x: x[1]):
                print(f"{filename:25s} {avg_time:.6f}s")
    
    else:
        # Benchmark single file
        benchmark_parse(args.file, args.iterations)

if __name__ == "__main__":
    main()
