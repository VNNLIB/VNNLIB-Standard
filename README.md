# GENG5511

A collaborative/shared repo for this project.

Contributors: Allen Anthony, Ann Roy <br>
Project: Enhancing VNNLib Spec

## Testing Instructions
1. Build the parser
```bash
$ bnfc -d -m VNNLib_bnf.cf  &&  make
```
2. Test the parser
   - the test files must be in the `/tests` folder
   - the examples are taken from the [VNNLIB Benchmarks Repo](https://github.com/VNNLIB/Benchmarks/) or lines of valid commands
```bash
$ echo "$(cat test/test1.vnnlib)" | VNNLibBnf/Test
```

**NOTE: there must be a space(` `) between the `TensorName` and `Subscript` for an element eg `X _0` instead of `X_0`. This is NOT in the VNNLib spec and must be fixed.**