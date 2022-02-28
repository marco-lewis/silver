from SilVer import SilVer
import z3

folder = "tests/"

def check(json_file, func, expected, verbose=False, stats=True, solver="z3"):
    silver = SilVer()
    sat = silver.verify_func(folder + json_file, func, verbose)
    if sat == expected:
        print("Test passed as expected")
    if verbose and sat == z3.sat:
        print(silver.solver.model())
    if sat != expected:
        raise Exception("SatError: Expected " + str(expected) + " but got " + str(sat))
    if stats:
        stats = silver.solver.statistics()
        print(stats.get_key_value('time'))
        print(stats.get_key_value('final checks'))

# check("test_singlevar.json", "main", z3.sat)
# check("test_unitary.json", "main", z3.sat)
# check("uint.json", "uint_test", z3.sat)
# check("deutsch.json", "deutsch", z3.unsat, True)
# check("types.json", "main", z3.sat)

# check("deutsch_anc.json", "deutsch", z3.unsat)
# check("deutsch_anc2.json", "deutsch", z3.unsat)

# Next fails on purpose - gives a model
# check("deutsch_anc_fail.json", "deutsch", z3.unsat, True)

# Works after a while without summation in measurement
# Randomly gets fast
# check("grover_fixed.json", "grover_fixed", z3.unsat)
# check("had_loop.json", "had_loop", z3.unsat, True)
# check("grover_fixed2.json", "groverDiffusion", z3.unsat, True)
# check("grover_fixed2.json", "grover", z3.unsat)