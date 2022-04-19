from SilVer import SilVer
import z3

folder = "tests/"

def check(json_file, func, expected, verbose=False, stats=True, timeout=5000):
    silver = SilVer()
    silver.solver.set(timeout=timeout)
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

# Basic checks that SilVer compiles correctly
# check("test_singlevar.json", "main", z3.sat)
# check("test_unitary.json", "main", z3.sat)
# check("uint.json", "uint_test", z3.sat)
# check("types.json", "main", z3.sat)

# Verification of Deutsch's algorithm
# check("deutsch.json", "deutsch", z3.unsat)
# check("deutsch_anc.json", "deutsch", z3.unsat)
# check("deutsch_anc2.json", "deutsch", z3.unsat)

# Verification fail on purpose - gives a model
# check("deutsch_anc_fail.json", "deutsch", z3.unsat, True)

# Verification of Deutsch-Jozsa
# check("dj_fixed2.json", "fixed_dj", z3.unsat)
# check("dj_fixed3.json", "fixed_dj", z3.unsat, True)

# Verification of Grover's Algorithm - Work in Progress
# 2 qubits
# check("grover_fixed.json", "grover_fixed", z3.unsat)
# 3 qubits
# check("grover_fixed2.json", "grover_fixed", z3.unsat)