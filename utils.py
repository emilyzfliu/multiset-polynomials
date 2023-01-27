from math import cos, sin, pi

class Multiset():
    def __init__(self, s):
        self.s = s

    def __getitem__(self, idx):
        return self.s[idx]

    def has_value(self, value):
        return self.s.count(value)

class LagrangeBasesOfUnity():
    def __init__(self, n):
        self.n = n
    
    def __getitem__(self, i):
        return lambda x: self._lagrange_polynomial(i, x)

    def _lagrange_polynomial(self, i, x):
        total = 1
        ith_root = self._kth_root_of_unity(i)
        for j in range(self.n):
            if i != j:
                jth_root = self._kth_root_of_unity(j)
                total *= (x - jth_root) / (ith_root - jth_root)
        return total

    def _kth_root_of_unity(self, k):
        return cos(2*k*pi/self.n) + sin(2*k*pi/self.n)*1j


class StandardPoly():
    def __init__(self, coefficients):
        pass


def main():
    L = LagrangeBasesOfUnity(3)

    for i in range(3):
        root = L._kth_root_of_unity(i)
        for j in range(3):
            print(f'L_{j}(omega^{i}) = {L[j](root)}')



if __name__ == '__main__':
    main()
