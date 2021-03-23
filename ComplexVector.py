from complex import Complex

def ComplexVector(a, sz):
        cv = []
        for i in range(sz):
            token = a + '__' + str(i)
            z = Complex(token)
            cv.append(z)
        return cv