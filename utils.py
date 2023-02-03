from math import cos, sin, pi


# useful classes
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

class RootsOfUnity():
    '''
    Calculates the Nth roots of unity.
    '''
    def __init__(self, N):
        self.N = N
    
    def omega(self, k):
        '''Returns the kth Nth root of unity, omega^k.'''
        return cos(2*k*pi/self.N) + sin(2*k*pi/self.N)*1j

class LagrangeBasesOfUnity():
    '''
    Represents the Lagrange Basis of the n polynomials over the nth roots of unity.
    '''
    def __init__(self, n):
        self.n = n
        self.roots = RootsOfUnity(self.n)
    
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
        ith_root = self.roots.omega(i)
        for j in range(self.n):
            if i != j:
                jth_root = self.roots.omega(j)
                total *= (x - jth_root) / (ith_root - jth_root)
        return total

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

class LagrangeInterpolationPoly():
    '''
    Represents a set of numbers and evaluations in polynomial form
    '''
    def __init__(self, xs, ys):
        '''
        Creates a polynomial that is a Roots Representation of the first `m` elements of a multiset.
        This polynomial has value `a` as a root with multiplicity `k`
        iff `a` appears `k` times in the multiset.
        '''
        n = len(xs)
        polys = []
        coeffs = []
        for i in range(n):
            term = RootsRepPoly(xs[:i] + xs[i+1:])
            denom = 1
            for j in range(n):
                if j == i:
                    continue
                denom += (xs[i] - xs[j])
            denom = modular_inverse(denom)
            polys.append(term)
            coeffs.append((ys[i]*denom))

        self.polys = polys
        self.coeffs = coeffs
        self.n = n

    def evaluate(self, x):
        '''
        Evaluates Lagrange polynomial at point x.
        '''
        total = 0
        for i in range(self.n):
            total += self.coeffs[i]*self.polys[i].evaluate(x)
        return total

class Commit:
    '''
    Represents a cryptographic commitment to a polynomial x (e.g., KZG).
    '''

    def __init__(self, x, g=1):
        '''
        Creates a commitment to polynomial `x`.
        For this toy example, we simply store x in plaintext.

        x: polynomial to be committed to
        g: the generator of a group, to be used if we actually did KZG commitment
        '''
        self.g = g
        self.x = x

    def open(self):
        '''
        Opens the commitment to the polynomial, exposing it in plaintext.
        '''
        return self.x

INVERSES_DICT = {}

def modular_inverse(x, p=101):
    '''
    Computes modular inverse of x in base p.
    '''
    if x in INVERSES_DICT:
        return INVERSES_DICT[x]
    def extended_euclidean(a, b):
        '''
        returns gcd, w, z such that aw + bz = gcd
        '''
        if a == 0:
            return b, 0, 1
        
        gcd, ww, zz = extended_euclidean(b % a, a) # ww * (b%a) + zz * a = gcd

        w = zz - (b//a) * ww
        z = ww
        return gcd, w, z
    _, _, inv = extended_euclidean(p, x) # gcd = 1 = wp + zx = zx mod p, x^-1 = z
    inv = (inv + p) % p
    INVERSES_DICT[x] = inv
    INVERSES_DICT[inv] = x
    return inv

def main():
    n = 32

    L = LagrangeBasesOfUnity(n)

    for i in range(n):
        root = L._kth_root_of_unity(i)
        for j in range(n):
            print(f'L_{j}(omega^{i}) = {round(L[j](root).real)}')



if __name__ == '__main__':
    main()
