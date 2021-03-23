from complex import Complex

def ComplexVector(a, sz, offset = 0):
        cv = []
        for i in range(offset, offset + sz):
            token = a + '__' + str(i)
            z = Complex(token)
            cv.append(z)
        return cv