from math import cos, sin, pi

class Multiset():
    '''
    Represents a multiset.
    '''
    def __init__(self, s):
        '''
        Creates a multiset from list `s`, where element a with multiplicity k in the multiset
        appears k times in `s`.
        '''
        self.s = s

    def __getitem__(self, idx):
        return self.s[idx]

    def has_value(self, value):
        return self.s.count(value)

    def standard_rep(self):
        '''
        Returns the Standard Representation polynomial form of this multiset.
        '''
        return StandardRepPoly(self.s)
    
    def roots_rep(self, m=None):
        '''
        Returns the up-to-m Roots Representation polynomial form of this multiset.
        '''
        return RootsRepPoly(self.s, m)

class LagrangeBasesOfUnity():
    '''
    Represents the Lagrange Basis of the n polynomials over the nth roots of unity.
    '''
    def __init__(self, n):
        self.n = n
    
    def __getitem__(self, i):
        '''
        Returns the Lagrange Basis polynomial for the ith of the nth roots of unity.
        '''
        return lambda x: self._lagrange_polynomial(i, x)

    def _lagrange_polynomial(self, i, x):
        '''
        Returns L_i(x), i.e. the evaluation of the ith nth root of unity at x.
        '''
        total = 1
        ith_root = self._kth_root_of_unity(i)
        for j in range(self.n):
            if i != j:
                jth_root = self._kth_root_of_unity(j)
                total *= (x - jth_root) / (ith_root - jth_root)
        return total

    def _kth_root_of_unity(self, k):
        '''
        Returns the kth of the nth roots of unity.
        '''
        return cos(2*k*pi/self.n) + sin(2*k*pi/self.n)*1j

class StandardRepPoly():
    '''
    Represents a multiset in its "Standard Representation" polynomial form.
    '''
    def __init__(self, coefficients):
        '''
        Creates a polynomial that is a Standard Representation of a multiset
        with `coefficients` as its elements.
        '''
        self.coefficients = coefficients
        self.n = len(self.coefficients)
        self.L = LagrangeBasesOfUnity(self.n)

    def evaluate(self, x):
        '''
        Evaluates this Standard Representation polynomial at point x.
        '''
        total = 0
        for i, a_i in enumerate(self.coefficients):
            total += a_i * self.L[i](x)
        return total

class RootsRepPoly():
    '''
    Represents a multiset in its "Roots Representation" polynomial form.
    '''
    def __init__(self, roots, m=None):
        '''
        Creates a polynomial that is a Roots Representation of the first `m` elements of a multiset.
        This polynomial has value `a` as a root with multiplicity `k`
        iff `a` appears `k` times in the multiset.
        '''
        self.roots = roots
        self.n = len(self.roots)
        self.m = m if m is not None else self.n

    def evaluate(self, x):
        '''
        Evaluates this Roots Representation polynomial at point x.
        '''
        total = 1
        for i in range(self.m):
            total *= (x - self.roots[i])
        return total


class InverseRepPoly():
    def __init__(self, vals):
        '''Creates an inverse representation polynomial'''
        self.vals = vals
        self.n = len(self.vals)
    
    def evaluate(self, x, m=None):
        '''Evaluates first m terms of inverse representation at point x'''
        m = m if m is not None else self.n
        total = 0
        for i in range(m):
            total += 1/(x - self.vals[i])
        return total

def main():
    n = 32

    L = LagrangeBasesOfUnity(n)

    for i in range(n):
        root = L._kth_root_of_unity(i)
        for j in range(n):
            print(f'L_{j}(omega^{i}) = {round(L[j](root).real)}')



if __name__ == '__main__':
    main()
