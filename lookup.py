'''
Implementation of lookup argument in https://zkresear.ch/t/new-lookup-argument/32.
'''
from utils import Commit, FiniteField
import random

# we will work over the finite field Z_101 as a toy example
P = 101
# our multiplicative subgroup will be [1, ..., 11]
N = 11
OMEGA = 2 # a generator of the subgroup
SUBGROUP_INVERSES = {
    1 : 1,
    2 : 6,
    3 : 4,
    4 : 3,
    5 : 9,
    6 : 2,
    7 : 8,
    8 : 7,
    9 : 5,
    10 : 10,
}

# Prover/Verifier sharing a reference to the ModularInverter instantiated in F
# will lead to minor speedup due to mutually accessible cachings of computed inverses
F = FiniteField(P, N, OMEGA, SUBGROUP_INVERSES)
LAGRANGE_BASIS = F.lagrange_basis

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
        self.L = LAGRANGE_BASIS

    def evaluate(self, x):
        '''
        Evaluates this Standard Representation polynomial at point x.
        '''
        total = 0
        for i, a_i in enumerate(self.coefficients):
            total += a_i * self.L[i](x)
        return total % P

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
        return total % P

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
        return total % P

class LagrangeInterpolationPoly():
    '''
    Represents a set of numbers and evaluations in polynomial form
    '''
    def __init__(self, F, xs, ys):
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
            denom = F.modular_inverter.modular_inverse(denom)
            polys.append(term)
            coeffs.append((ys[i]*denom))

        self.F = F
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
        return total % self.F.P

class Z_H:
    '''
    Represents the vanishing polynomial for the multiplicative subgroup
    contained within the finite field `F`.

    The polynomial Z() whose existence is asserted as part of step 3 is only specified to vanish
    over the Nth roots of unity, so we divide by the vanishing polynomial of the Nth roots
    to confirm Z()'s polynomialness.

    Z_H is public because it is specified wholly by N.
    '''
    def __init__(self, F):
        self.F = F
    
    def evaluate(self, x):
        '''Computes Z_H(x).'''
        total = 1
        for k in range(self.F.N):
            total *= (x - (self.F.omega**k))
        return total % self.F.P


class Prover:
    def __init__(self, A, B):
        '''
        Creates a Prover engaging in this protocol.
        '''
        self.view = {} # represents the "view" of the Prover: all information visible to them during the interactive protocol
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
                return (ret*self.extra_poly.evaluate(x)) % P
        
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
                self.omegas = [] #TODO: omega**k for k in range self.N + 1
                self.evals = [self.z_omega(k) for k in range(self.N+1)]
                self.poly = LagrangeInterpolationPoly(self.F, self.omegas, self.evals)
            
            def z_omega(self, k):
                '''Evaluates Z(omega^k).'''
                return (self.Z1 - (self.y / self.N) * k + self.W.evaluate(self.gamma, k)) % P
            
            def evaluate(self, x):
                return self.poly.evaluate(x) % P

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
                return (ret / self.Z_H.evaluate(k)) % P

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
    def __init__(self, B):
        '''
        Creates a Verifier engaging in this protocol.
        '''
        self.view = {} # represents the "view" of the Verifier: all information visible to them during the interactive protocol
        self.view['B'] = B
    
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
        gamma = random.randint(0, P)
        self.view['gamma'] = gamma
        return {'gamma': gamma}

    def step4(self):
        '''Verifier issues a second challenge, called delta, for t'''
        delta = random.randint(0, P)
        self.view['delta'] = delta
        return {'delta': delta}
    
    def step6(self):
        '''Verifier checks the equalities for their two challenges'''
        R_g = self.view['R(gamma)']
        y = self.view['y']
        Z_B_g = self.view['Z_B(gamma)']
        t_d = self.view['t(delta)']
        Z_wd = self.view['Z(w*delta)']
        Z_d = self.view['Z(delta)']
        gamma = self.view['gamma']
        A_d = self.view['A(delta)']
        delta = self.view['delta']
        Z_H_d = Z_H(F).evaluate(delta)


        # check gamma equality
        gamma_equality = ((R_g * y) % P == Z_B_g)

        # check delta equality
        delta_equality = (t_d == (((Z_wd - Z_d + y/N)*(gamma - A_d) - 1) / Z_H_d) % P)
        return 'accept' if gamma_equality and delta_equality else 'reject'

def main():
    # the premise is that A is private to the prover, but B is publicly known
    A = [1, 2, 7]
    B = [1, 2, 3, 7, 9]

    # routine assertions — otherwise the protocol doesn't apply as this isn't an accepting instance of the language
    assert N < F
    assert len(A) <= N
    assert len(B) <= N
    assert set(A).issubset(set(B))

    prover = Prover(A, B)
    verifier = Verifier(B)

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


if __name__ == '__main__':
    main()
