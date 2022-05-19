from SilVer import SilVer
import z3
from statistics import mean
import os, contextlib

folder = "tests/"
def get_time(json_file, func, expected, seed, timeout=60000):
    with open(os.devnull, "w") as f, contextlib.redirect_stdout(f):
        silver = SilVer(timeout, seed=seed)
        sat = silver.verify_func(folder + json_file, func)
        stats = silver.solver.statistics()    
    return sat == expected, stats.time

def benchmark(json_file, func, expected):
    t_correct = []
    t_unkown = []
    print('Benchmarking ' + json_file)
    max = 11
    print ('0/10', end='\r', flush=True)
    for i in range(1, max):
        res, time = get_time(json_file, func, expected, i)
        if res: t_correct.append(time)
        else: t_unkown.append(time)
        print(str(i) + '/' + str(max-1), end='\r', flush=True)

    print()
    print('Total Runtime: ' + str(sum(t_correct) + sum(t_unkown)))
    print('Average time: ' + str(mean(t_correct)))

benchmark("dj_fixed2.json", "fixed_dj", z3.unsat)
benchmark("dj_fixed3.json", "fixed_dj", z3.unsat)
benchmark("dj_fixed4.json", "fixed_dj", z3.unsat)
benchmark("dj_fixed5.json", "fixed_dj", z3.unsat)
benchmark("dj_fixed6.json", "fixed_dj", z3.unsat)