from utils import *
import random

'''
    Multiset "union" check for A, B, C
'''
P = 10**9 + 7

def challenge():
    return random.randint(0, P)

def main():
    # define A, B, C (known only by prover)
    A = []
    B = []
    C = []

    z_A = RootsRepPoly(A)
    z_B = RootsRepPoly(B)
    z_C = RootsRepPoly(C)

    gamma = challenge()

    assert z_A.evaluate(gamma) * z_B.evaluate(gamma) == z_C.evaluate(gamma)

if __name__ == '__main__':
    main()