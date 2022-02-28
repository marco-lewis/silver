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
        
check("deutsch_program1.json", "deutsch", z3.unsat)
check("deutsch_program2.json", "deutsch", z3.sat)