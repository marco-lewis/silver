import logging
import sys
sys.path.append('../silver')
from silver.silver.SilVer import SilVer
import z3, sys

folder = "examples/Silq_Programs/"

def check(json_file, func, expected, log_level=logging.WARNING, stats=False, timeout=5000, seed=3, check_store=False):
    silver = SilVer(timeout=timeout, seed=seed, check_store=check_store)
    sat = silver.verify_func(folder + json_file, func, log_level)
    if sat == expected: logging.info("Test passed as expected")
    else: logging.error("SatError: Expected %s but got %s", expected, sat)
    if sat == z3.sat:
        m = silver.solver.model()
        logging.info("Model/CEX: %s", m)
        f = z3.Function('f', z3.IntSort(), z3.IntSort())
        if f in m: logging.info('Function: %s', m[f])
    if sat == z3.unsat: logging.info("Unsat core: %s", silver.solver.unsat_core())
    if sat == z3.unknown: logging.info('Reason: %s', silver.solver.reason_unknown())
    silver_stats = silver.solver.statistics()
    try: logging.info("Time (s) %s", silver_stats.get_key_value('time'))
    except: logging.info("Unable to get time (possibly 0)")
    if stats: logging.info("Stats:\n%s", silver_stats)
    sys.stdout.flush()