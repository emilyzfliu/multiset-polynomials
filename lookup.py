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

def step1(A, B):
    '''R = Z_B * W_A'''
    class R():
        # A = [a_1, a_2, ... a_N]
        # B = [b_1, b_2, ... b_n]
        # Assume A, B, dedup
        def __init__(self, elts_a, elts_b):
            self.elts_a = elts_a
            self.extra_elts = [x for x in elts_b if x not in elts_a]
            self.n = len(self.elts_a) # TODO this is wrong.
            # specifically A is probably passed in as n elements, and we're "supposed" to pad it to A' with elts from B.
            # so this defn of n is correct but the other stuff must be addressed, and in particular the comment up top on R is wrong.
            self.terms = []
            # the term for elt. i has the coefficients a_1,...,a_i-1,a_i+1,...,aN,(all elts of b not in a)
            # so we can factor out the (all elts of b not in a) term, then compute the a-elt terms separately
            for i in range(self.n):
                self.terms.append(RootsRepPoly(self.elts_a[:i] + self.elts_a[i+1:]))
            self.extra_poly = RootsRepPoly(self.extra_elts)
        
        def evaluate(self, x):
            ret = 0
            for term in self.terms:
                ret += term.evaluate(x)
            return ret*self.extra_poly.evaluate(x)
    A_c = Commit(StandardRepPoly(A))
    R_c = Commit(R(A, B))
    return A_c, R_c


def step2():
    '''
    The Verifier issues a challenge uniformly sampled from the finite field.
    
    By the Schwartz-Zippel lemma, the probability that a malicious Prover can issue fradulent polynomials
    yet still have the polynomial identities coincidentally check out on this uniformly
    sampled field point is quite low, assuming the polynomials have degree << |F|.
    '''
    return random.randint(0, P)


def step3(gamma, A, B):
    class Z():
        '''
        Represents the polynomial Z which is asserted to exist and have particular properties
        via a Grand Product Argument. Z satisfying these properties on the roots of unity
        will imply that W_A(gamma) = y.
        '''
        def __init__(self, gamma, W, Z1 = 0):
            self.gamma = gamma
            self.W = W
            self.N = self.W.n # the order of the roots of unity Z is evaluated over
            self.y = W.evaluate(self.gamma, self.N)
            self.Z1 = Z1 # the value that Z takes on at Z(1) = Z(omega^0) = Z(omega^N)
        
        def evaluate(self, k):
            '''Evaluates Z(omega^k).'''
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
        
        def evaluate(self, k):
            '''Evaluates t(omega^k)'''
            # Recall that Z.evaluate(k) := Z(omega^k)
            ret = self.Z.evaluate(k+1) - self.Z.evaluate(k) + self.y/self.N
            ret *= gamma - self.A.evaluate(k)
            ret -= 1
            return ret / self.Z_H.evaluate(k)

    A_poly = StandardRepPoly(A)
    W_A = InverseRepPoly(A)
    Z = Z(gamma, W_A)
    Z_c = Commit(Z)
    y = W_A(gamma)
    t_c = Commit(t(Z, y, gamma, A_poly))
    Z_B = RootsRepPoly(B)
    return Z_c, t_c, y, Z_B.evaluate(gamma)


def step4():
    '''Verifier issues a second challenge, called delta'''
    return random.randint(0, P)


def step5(gamma, delta, R, Z, t, A):
    '''Prover collates all the information the Verifier needs to check the equality'''
    return R.evaluate(gamma), Z.evaluate(delta), Z.evaluate(delta+1), t.evaluate(delta), A.evaluate(delta)


def step6(Rg, y, ZBg, td, Zdw, Zd, N, gamma, Ad, ZH = 1):
    '''Verifier checks the equalities for their two challenges'''
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