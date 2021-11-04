EXPTYPE = "expType"
TYPEOBJ = "typeObj"

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