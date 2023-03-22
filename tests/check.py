import logging
import sys
sys.path.append('../silver')
from silver.silver.SilVer import SilVer
import z3, sys

folder = "examples/Silq_Programs/"
logger = logging.getLogger("check")

def check(json_file, func, expected, log_level=logging.INFO, spq_file=None, stats=False, timeout=5000, seed=3, check_store=False):
    logging.basicConfig(level=log_level)
    logger.info("Starting check on %s in %s", func, json_file)
    silver = SilVer(timeout=timeout, seed=seed, check_store=check_store)
    sat = silver.verify_func(folder + json_file, func, log_level=log_level, spq_file=spq_file)
    if sat == expected: logger.info("Test passed as expected")
    else: logger.error("TestError: Expected %s but got %s", expected, sat)
    if sat == z3.sat:
        m = silver.solver.model()
        logger.debug("Model/CEX:\n%s", m)
        f = z3.Function('f', z3.IntSort(), z3.IntSort())
        if f in m: logger.debug('Function: %s', m[f])
    if sat == z3.unsat: logger.debug("Unsat core:\n%s", silver.solver.unsat_core())
    if sat == z3.unknown: logger.debug('Reason: %s', silver.solver.reason_unknown())
    silver_stats = silver.solver.statistics()
    try: logger.info("Time (s) %s", silver_stats.get_key_value('time'))
    except: logger.info("Unable to get time (possibly 0)")
    if stats: logger.info("Stats:\n%s", silver_stats)
    logger.info("Done.")
    sys.stdout.flush()