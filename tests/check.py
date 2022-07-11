import sys
sys.path.append('../silver')
from silver.SilVer import SilVer
import z3, sys

folder = "Silq_Programs/.ast/"

def check(json_file, func, expected, verbose=False, stats=True, show_objects=False, timeout=5000):
    if show_objects and not(verbose): print("Verbosity: objects will not be shown as verbose is not enabled.")
    silver = SilVer(timeout=timeout)
    sat = silver.verify_func(folder + json_file, func, verbose, show_objects)
    if sat == expected: print("Test passed as expected")
    else: print("SatError: Expected " + str(expected) + " but got " + str(sat))
    if verbose and sat == z3.sat:
        print("Model/CEX")
        m = silver.solver.model()
        print(m)
        try: print('Function: ', m[z3.Function('f', z3.IntSort(), z3.IntSort())])
        except: pass
    if verbose and sat == z3.unknown:
        print('Reason: ', silver.solver.reason_unknown())
    if verbose and sat == z3.unsat:
        print("Unsat Core:")
        print(silver.solver.unsat_core())
    stats = silver.solver.statistics()    
    if stats:
        print("Time")
        try: print(stats.get_key_value('time'))
        except: print("Unable to get time (possibly 0)")
        if verbose:
            print("Stats")
            print(stats)
    print()
    sys.stdout.flush()