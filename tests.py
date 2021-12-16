from SilVer import SilVer

def check(json_file, func, verbose=False):
    silver = SilVer()
    sat = silver.verify_func(json_file, func, verbose)
    print(sat)
    if verbose:
        print(silver.solver.model())
    
check("test_singlevar.json", "main")
check("test_unitary.json", "main")
check("uint.json", "uint_test")
check("types.json", "main")
check("deutsch.json", "deutsch", True)