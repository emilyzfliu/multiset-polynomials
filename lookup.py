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

class Z_H:
    '''
    Represents the vanishing polynomial for the Nth roots of unity.

    The polynomial Z() whose existence is asserted as part of step 3 is only specified to vanish
    over the Nth roots of unity, so we divide by the vanishing polynomial of the Nth roots
    to confirm Z()'s polynomialness.

    Z_H is public because it is specified wholly by N.
    '''
    def __init__(self, N):
        self.N = N
        self.roots = RootsOfUnity(self.N)
    
    def evaluate(self, x):
        '''Computes Z_H(x).'''
        total = 1
        for i in range(self.N):
            total *= (x - self.roots.omega(i))
        return total


class Prover:
    def __init__(self, N, A, B):
        self.view = {} # represents the "view" of the Prover: all information visible to them during the interactive protocol
        self.view['N'] = N
        self.view['A'] = A
        self.view['B'] = B

    def receive(self, message):
        '''
        Records a message sent by the Verifier.

        `message`: a dictionary of strings to values representing the contents of a message
        in the interactive protocol
        '''
        self.view.update(**message)
    
    def step1(self):
        '''R = Z_B * W_A'''
        class R():
            # A = [a_1, a_2, ... a_N]
            # B = [b_1, b_2, ... b_n]
            # assume A, B are deduplicated
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
        
        A = self.view['A']
        B = self.view['B']
        output = {'A_c': Commit(StandardRepPoly(A)),
                  'R_c': Commit(R(A, B))}
        self.view.update(**output)
        return output

    def step3(self):
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
                ret *= self.gamma - self.A.evaluate(k)
                ret -= 1
                return ret / self.Z_H.evaluate(k)

        A = self.view['A']
        B = self.view['B']
        gamma = self.view['gamma']

        A_poly = StandardRepPoly(A)
        W_A = InverseRepPoly(A)
        y = W_A(gamma)
        Z_B = RootsRepPoly(B)

        self.view['Z'] = Z(gamma, W_A)
        self.view['t'] = t(Z, y, gamma, A_poly)

        output = {'Z_c': Commit(self.view['Z']),
                  'y': y,
                  't_c': Commit(self.view['t']),
                  'Z_B(gamma)': Z_B.evaluate(gamma)}
        self.view.update(**output)
        return output

    def step5(self):
        '''Prover collates all the information the Verifier needs to check the equality'''
        gamma = self.view['gamma']
        delta = self.view['delta']
        R = self.view['R']
        Z = self.view['Z']
        t = self.view['t']
        A = self.view['A']

        # I guess the prover could save this but they don't need to?
        output = {'R(gamma)': R.evaluate(gamma),
                  'Z(delta)': Z.evaluate(delta),
                  'Z(w*delta)': Z.evaluate(delta+1),
                  't(delta)': t.evaluate(delta),
                  'A(delta)': A.evaluate(delta)}
        return output

class Verifier:
    def __init__(self, N, B):
        self.view = {} # represents the "view" of the Verifier: all information visible to them during the interactive protocol
        self.view['N'] = N
        self.view['B'] = B
        # TODO refactor as multiset
    
    def receive(self, message):
        '''
        Records a message sent by the Prover.

        `message`: a dictionary of strings to values representing the contents of a message
        in the interactive protocol
        '''
        self.view.update(**message)

    def step2(self):
        '''
        The Verifier issues a challenge uniformly sampled from the finite field to check R.
        
        By the Schwartz-Zippel lemma, the probability that a malicious Prover can issue fradulent polynomials
        yet still have the polynomial identities coincidentally check out on this uniformly
        sampled field point is quite low, assuming the polynomials have degree << |F|.
        '''
        output = {'gamma': random.randint(0, P)}
        self.view.update(**output)
        return output

    def step4(self):
        '''Verifier issues a second challenge, called delta, for t'''
        output = {'delta': random.randint(0, P)}
        self.view.update(**output)
        return output
    
    def step6(self, Rg, y, ZBg, td, Zdw, Zd, N, gamma, Ad, ZH = 1):
        '''Verifier checks the equalities for their two challenges'''
        output = {'R(gamma)': R.evaluate(gamma),
                  'Z(delta)': Z.evaluate(delta),
                  'Z(w*delta)': Z.evaluate(delta+1),
                  't(delta)': t.evaluate(delta),
                  'A(delta)': A.evaluate(delta)}

        R_g = self.view['R(gamma)']
        y = self.view['y']
        Z_B_g = self.view['Z_B(gamma)']
        t_d = self.view['t(delta)']
        Z_wd = self.view['Z(w*delta)']
        Z_d = self.view['Z(delta)']
        N = self.view['N']
        gamma = self.view['gamma']
        A_d = self.view['A(delta)']
        delta = self.view['delta']
        Z_H_d = Z_H(N).evaluate(delta)


        # check gamma equality
        gamma_equality = (Rg * y == ZBg)

        # check delta equality
        delta_equality = (td == ((Zdw - Zd + y/N)*(gamma - Ad) - 1) / ZH)
        return 'accept' if gamma_equality and delta_equality else 'reject'

def main():
    # TODO refactor with these as Multisets
    N = 16
    A = [1, 2, 7]
    B = [1, 2, 3, 7, 9]
    # the premise is that A is private to the prover, but B is publicly known
    prover = Prover(N, A, B)
    verifier = Verifier(N, B)

    message1 = prover.step1()
    verifier.receive(message1)

    message2 = verifier.step2()
    prover.receive(message2)
    
    message3 = prover.step3()
    verifier.receive(message3)

    message4 = verifier.step4()
    prover.receive(message4)

    message5 = prover.step5()
    verifier.receive(message5)

    message6 = verifier.step6()
    if message6 == 'accept':
        print('Verifier accepted the proof :)')
    else:
        print('Verifier rejected the proof :(')


    # Step 1 commitments for A and R
    # - evaluate R?
    prover_view.update(**step1(A, B))
    A_c = prover_view['A_c']
    R_c = prover_view['R_c']

    # Step 2 send random gamma
    verifier_view.update(**step2())
    gamma = verifier_view['gamma']

    # Step 3 compute and send Z, t, y, Z_b gamma
    prover_view.update(**step3(A, B))
    # Z_c, t_c, y, Z_b = step3(A, B)

    # Step 4 send random delta
    verifier_view.update(**step4())
    delta = verifier_view['delta']

    # Step 5
    # $R(\gamma)$, $Z(\delta)$, $Z(\omega \delta)$, $t(\delta)$, $A(\delta)$, $Z_H(\delta)$.
    Rg, Zd, Zdw, td, Ad = step5(gamma, delta, R_c, Z_c, t_c, A_c)

    # Step 6
    step6(Rg, y, Z_b, td, Zdw, Zd, len(A), gamma, Ad)



if __name__ == '__main__':
    main()