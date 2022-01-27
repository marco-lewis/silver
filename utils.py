import re
from z3 import *

EXPTYPE = "expType"
TYPEOBJ = "typeObj"

def delta(i, j):
    return 1 if i == j else 0

def kronecker(matrix1, matrix2):
    """
    Performs the Kronecker product on 2 list of lists

    Source: 
        http://rosettacode.org/wiki/Kronecker_product#Python

    Args:
        matrix1 (T[][]): First list to be used in operation
        matrix2 (T[][]): Second list to be used in the operation

    Returns:
        T[][]: matrix1 ⊗ matrix2
    """
    return [[num1 * num2 for num1 in elem1 for num2 in matrix2[row]] for elem1 in matrix1 for row in range(len(matrix2))]
 
def dot(A, B):
    """
    Performs matrix multiplication on 2 lists of lists
    
    Source:
        http://www.rosettacode.org/wiki/Matrix_multiplication#Python
        
    Args:
        A (T[][]): First list to be used in operation
        B (T[][]): Second list to be used in the operation

    Returns:
        T[][]: A.B
    """
    return [[sum(x * B[i][col] for i,x in enumerate(row)) for col in range(len(B[0]))] for row in A]

def generate_silspeq_from_func(func, args, ret):
    """
    Generates the string for a SilSpeq file from given strings.

    Args:
        func ([type]): [description]
        args ([type]): [description]
        ret ([type]): [description]
    """
    speq = func + "("
    for arg in args:
        speq += arg + ","
    if speq[-1] == ",":
        speq = speq[:-1]
    speq += ")->(" + ret + ")\npre{\n\n}\npost{\n\n}"
    return speq

def convert_type_to_Z3_literal(type):
    if (re.match(r"[N|ℕ]", type)):
        return IntSort()
    if (re.match(r"[B|𝔹]", type)):
        return IntSort()
    if (re.match(r"uint\[[0-9]+\]", type)):
        return IntSort()
    if (re.match(r".*(→.*)+",type)):
        types = [convert_type_to_Z3_literal(arg_type)
                    for arg_type in re.split(r"→", type)]
        return tuple(types)
    if (re.match(r"[¬, const, qfree].*", type)):
        split = re.split(r"[¬, const, qfree]", type, maxsplit=1)[1]
        return convert_type_to_Z3_literal(split)
    raise Exception("TypeTODO: " + type)