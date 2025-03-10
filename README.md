# GENG5511

A collaborative/shared repo for this project.

Contributors: Allen Anthony, Ann Roy <br>
Project: Enhancing VNNLib Spec

## Testing Instructions
A build and test bash script has been provided for building & testing the generated parser for the grammar file which run the test on all the files in `test/`.  
If the `test.sh` does not allow execution, add permissions accordingly:
```bash
$ chmod +x test.sh
```

1. Build the parser
```bash
$ bnfc -d -m VNNLib_bnf.cf  &&  make
```
2. Test the parser
   - the test files must be in the `/tests` folder
   - the examples are taken from the [VNNLIB Benchmarks Repo](https://github.com/VNNLIB/Benchmarks/) or lines of valid commands
```bash
$ VNNLibBnf/Test <test-file-path>
```
