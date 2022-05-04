from SilVer import SilVer
import z3

folder = "tests/"

def check(json_file, func, expected, verbose=False, stats=True, timeout=5000):
    silver = SilVer(timeout)
    sat = silver.verify_func(folder + json_file, func, verbose)
    if sat == expected: print("Test passed as expected")
    if verbose and sat == z3.sat:
        print("Model/CEX")
        m = silver.solver.model()
        print(m)
        try: print('Function: ', m[z3.Function('f', z3.IntSort(), z3.IntSort())])
        except: pass
    if verbose and sat == z3.unsat:
        print("Unsat Core:")
        print(silver.solver.unsat_core())
    if stats:
        print("Stats")
        stats = silver.solver.statistics()
        print(stats)
    if sat != expected:
        raise Exception("SatError: Expected " + str(expected) + " but got " + str(sat))
    print()

# Basic checks that SilVer compiles correctly
# check("test_singlevar.json", "main", z3.sat)
# check("test_unitary.json", "main", z3.sat)
# check("uint.json", "uint_test", z3.sat)
# check("types.json", "main", z3.sat, True)

# Verification of Deutsch's algorithm
# check("deutsch.json", "deutsch", z3.unsat)
# BUG: prog_obl not sat
# check("deutsch_anc.json", "deutsch", z3.unsat)
# check("deutsch_anc2.json", "deutsch", z3.unsat)

# Verification fail on purpose - gives a model
# BUG: prog_obl not sat
# check("deutsch_anc_fail.json", "deutsch", z3.unsat)

# Verification of Deutsch-Jozsa
# dj_fixed<n> - Deutsch-Jozsa for n-qubits
# check("dj_fixed2.json", "fixed_dj", z3.unsat)
# check("dj_fixed3.json", "fixed_dj", z3.unsat)
# check("dj_fixed4.json", "fixed_dj", z3.unsat)
# check("dj_fixed5.json", "fixed_dj", z3.unsat)
# check("dj_fixed6.json", "fixed_dj", z3.unsat)
# Very slow (kinda expected)
# check("dj_fixed7.json", "fixed_dj", z3.unsat)

# Verification of Grover's Algorithm - Work in Progress
# 2 qubits - uses certainty
# check("grover_fixed.json", "grover_fixed", z3.unsat)
# Rev
# check("grover_rev2.json", "grover_rev", z3.unsat)
# check("grover_rev3.json", "grover_rev", z3.unsat)
# check("grover_rev7.json", "grover_rev", z3.unsat)
# 3 qubits - problems with measurement/probability
# Likely causing check to be unknown
# check("grover_fixed2.json", "grover_fixed", z3.unsat)