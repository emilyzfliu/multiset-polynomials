'''
Utility functions used in `lookup.py` but not specific to the particular protocol.
'''

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

class ModularInverter:
    '''
    Class to wrap and memoize the computation of modular inverses in a particular finite field.
    '''
    def __init__(self, p=101):
        self.p = p
        self.inverses_dict = {}
    
    def modular_inverse(self, x):
        '''Computes modular inverse of x in this finite field'''
        if x in self.inverses_dict:
            return self.inverses_dict[x]

        def extended_euclidean(a, b):
            '''
            Returns gcd, w, z such that aw + bz = gcd
            '''
            if a == 0:
                return b, 0, 1
            
            gcd, ww, zz = extended_euclidean(b % a, a) # ww * (b%a) + zz * a = gcd

            w = zz - (b//a) * ww
            z = ww
            return gcd, w, z
        
        _, _, inv = extended_euclidean(self.p, x) # gcd = 1 = wp + zx = zx mod p, x^-1 = z
        inv = (inv + self.p) % self.p
        self.inverses_dict[x] = inv
        self.inverses_dict[inv] = x
        return inv
