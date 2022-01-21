from SilVer import SilVer
import z3

folder = "tests/"

def check(json_file, func, expected, verbose=False):
    silver = SilVer()
    sat = silver.verify_func(folder + json_file, func, verbose)
    if sat == expected:
        print("Test passed as expected")
    if sat != expected:
        raise Exception("SatError: Expected " + str(expected) + " but got " + str(sat))
    if verbose and sat == z3.sat:
        print(silver.solver.model())
    
check("test_singlevar.json", "main", z3.sat)
check("test_unitary.json", "main", z3.sat)
check("uint.json", "uint_test", z3.sat)
check("types.json", "main", z3.sat)
check("deutsch.json", "deutsch", z3.unsat)
# Possibly not working
check("deutsch_anc.json", "deutsch", z3.unsat)
# Not working yet
check("deutsch_anc2.json", "deutsch", z3.unsat)