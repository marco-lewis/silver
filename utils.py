# Source: http://rosettacode.org/wiki/Kronecker_product#Python

def kronecker(matrix1, matrix2):
    return [[num1 * num2 for num1 in elem1 for num2 in matrix2[row]] for elem1 in matrix1 for row in range(len(matrix2))]
 