from utils import *
import random

'''
    \item The prover sends KZG commitments of $R(\gamma)$, $Z(\delta)$, $Z(\omega \delta)$, $t(\delta)$, $A(\delta)$, $Z_H(\delta)$.
    \item The verifier checks the following:
    First, use $\gamma$ to check that $\mathcal{A}$ is included in $\mathcal{B}$ via the given definition:
    \begin{align*}
        R(\gamma) \cdot y = Z_B (\gamma)
    \end{align*}
    Then, check legitimacy of $y$ by using the $\delta$ commitments to verify the legitimacy of the $t$ and $Z$ polynomials:
    \begin{align*}
        t(\delta) = \frac{1}{Z_H(\delta)}\left(\left(Z(\omega \delta) - Z(\delta) + \frac{y}{N}\right) \left(\gamma - A(X)\right) - 1\right)
    \end{align*}

'''
P = 10**9 + 7

class Commit:
    def __init__(self, x, g=1):
        '''
        Some cryptographic commitment for x (eg: KZG). For now, we just return x for simplicity
        '''
        self.g = g
        self.x = x
    
    def open(self):
        return self.x

def step1(A, B):
    '''R = ZB * WA'''
    class R:
        # A = [a1, a2, ... aN]
        # B= [b1, b2, ... bn]
        # for elt. 1: a2*a3*...*aN * (all elts of b not in a)
        # Assume A, B, dedup
        def __init__(self, vals_a, vals_b):
            self.vals_a = vals_a
            self.extra_vals = [x for x in vals_b if x not in vals_a]
            self.n = len(self.vals)
            self.terms = []
            for i in range(self.n):
                self.terms.append(RootsRepPoly(self.vals_a[:i] + self.vals_a[i+1:]))
            self.extra_poly = RootsRepPoly(self.extra_vals)
        
        def evaluate(self, x):
            ret = 0
            for elem in self.terms:
                ret += elem.evaluate(x)
            return ret*self.extra_poly.evaluate(x)
    A_c = Commit(StandardRepPoly(A))
    R_c = Commit(R(A, B))
    return A_c, R_c

def step2():
    '''return gamma'''
    return random.randint(0, P)



def step3(gamma, A, B):
    class Z():
        def __init__(self, gamma, W, Z1 = 0):
            self.gamma = gamma
            self.W = W
            self.N = self.W.n
            self.y = W.evaluate(self.gamma, self.N)
            self.Z1 = Z1
        
        def evaluate(self, k):
            '''Z(omega**k)'''
            return self.Z1 - (self.y / self.N) * k + self.W.evaluate(self.gamma, k)

    class t():
        #  t(x) := \frac{1}{Z_H(X)} \left(\left(Z(\omega X) - Z(X) + \frac{y}{N}\right) \left(\gamma - A(X)\right) - 1\right)
        def __init__(self, Z, y, gamma, A):
            self.Z_H = RootsRepPoly([])
            self.Z = Z
            self.y = y
            self.gamma = gamma
            self.A = A
            self.N = self.Z.N
        
        def evaluate(self, x):
            # Z.evaluate(k) := Z(omega**k)
            ret = self.Z.evaluate(x+1) - self.Z.evaluate(x) + self.y/self.N
            ret *= gamma - self.A.evaluate(x)
            ret -= 1
            return ret / self.Z_H.evaluate(x)

    A_poly = StandardRepPoly(A)
    W_A = InverseRepPoly(A)
    Z = Z(gamma, W_A)
    Z_c = Commit(Z)
    t_c = Commit(t(Z, W_A(gamma), gamma, A_poly))
    Z_B = RootsRepPoly(B)
    return Z_c, t_c, y, Z_B.evaluate(gamma)


def step4():
    '''return delta'''
    return random.randint(0, P)


def step5(gamma, delta, R, Z, t, A):
    return R.evaluate(gamma), Z.evaluate(delta), Z.evaluate(delta+1), t.evaluate(delta), A.evaluate(delta)

def step6(Rg, y, ZBg, td, Zdw, Zd, N, gamma, Ad, ZH = 1):
    # check gamma equality
    assert Rg * y == ZBg

    # check delta equality
    assert td == ((Zdw - Zd + y/N)*(gamma - Ad) - 1)/ ZH


def main():
    # ideally multisets #TODO
    A = []
    B = []

    # Step 1 commitments for A and R
    # - evaluate R?
    A_c, R_c = step1(A, B)

    # Step 2 send random gamma
    gamma = step2()

    # Step 3 compute and send Z, t, y, Z_b gamma
    Z_c, t_c, y, Z_b = step3(A, B)

    # Step 4 send random delta
    delta = step4()

    # Step 5
    # $R(\gamma)$, $Z(\delta)$, $Z(\omega \delta)$, $t(\delta)$, $A(\delta)$, $Z_H(\delta)$.
    Rg, Zd, Zdw, td, Ad = step5(gamma, delta, R_c, Z_c, t_c, A_c)

    # Step 6
    step6(Rg, y, Z_b, td, Zdw, Zd, len(A), gamma, Ad)



if __name__ == '__main__':
    main()