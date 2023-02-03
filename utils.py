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
