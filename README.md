# EVNNLIB

A project to define and extend the grammar of the current VNNLIB specifications.  
Contributors: Allen Antony, Ann Roy, Matthew Daggitt <br>

## Set up
This project uses the BNFC package to build and test the parser.  
The set-up instructions can be found in the official documentation linked [here](https://hackage.haskell.org/package/BNFC-2.9.5).

## Testing Instructions
A build and test bash script has been provided for building & testing the generated parser for the grammar file which run the test on all the files in `test/`.  
If the `test.sh` does not allow execution, add permissions accordingly:
```bash
$ chmod +x test.sh
```

1. Build the parser
```bash
$ bnfc -d -m VNNLib_LBNF.cf  &&  make
```

**Note: to build the parser to C files, use the following command instead**
```bash
$ bnfc --c -m -o VNNLibLBNF VNNLib_LBNF.cf  &&  make -C VNNLibLBNF
```

2. Test the parser
   - the test files must be in the `/tests` folder
   - the examples are converted from the [VNNLIB Benchmarks Repo](https://github.com/VNNLIB/Benchmarks/) or lines of valid commands
```bash
$ VNNLibLBNF/Test <test-file-path>
```
**Note: if the C command was used, run the following command instead**
```bash
$ VNNLibLBNF/TestVNNLib_LBNF <test-file-path>
```