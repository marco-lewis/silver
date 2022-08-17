import sys
sys.path.append('../silver')
from silver.silver.SilVer import SilVer
import z3, sys

folder = "examples/Silq_Programs/"

def check(json_file, func, expected, verbose=False, stats=False, show_objects=False, timeout=5000, seed=3, check_store=False):
    if show_objects and not(verbose): print("Verbosity: objects will not be shown as verbose is not enabled.")
    silver = SilVer(timeout=timeout, seed=seed, check_store=check_store)
    sat = silver.verify_func(folder + json_file, func, verbose, show_objects)
    if sat == expected: print("Test passed as expected")
    else: print("SatError: Expected " + str(expected) + " but got " + str(sat))
    if verbose and sat == z3.sat:
        m = silver.solver.model()
        print("Model/CEX\n", m)
        f = z3.Function('f', z3.IntSort(), z3.IntSort())
        if f in m: print('Function: ', m[f])
    if sat == z3.unknown: print('Reason: ', silver.solver.reason_unknown())
    silver_stats = silver.solver.statistics()
    if verbose:
        print("Time (s)")
        try: print(silver_stats.get_key_value('time'))
        except: print("Unable to get time (possibly 0)")
        if stats: print("Stats\n", silver_stats)
    print()
    sys.stdout.flush()