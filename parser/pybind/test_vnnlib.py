import vnnlib
import os


print("Testing vnnlib parser")

file_path = os.path.dirname(os.path.abspath(__file__))
spec_path = os.path.join(file_path, "../../test/acc.vnnlib")

print("Parsing file: ", spec_path)

p = vnnlib.parse_vnnlib(spec_path)


