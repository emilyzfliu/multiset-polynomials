'''
Implementation of lookup argument in https://zkresear.ch/t/new-lookup-argument/32.
'''
from utils import Commit, ModularInverter, LagrangeBasis
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
MODULAR_INVERTER = ModularInverter(P)
LAGRANGE_BASIS = LagrangeBasis(N, OMEGA, SUBGROUP_INVERSES)

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
            total += MODULAR_INVERTER.modular_inverse(x - self.vals[i])
        return total % P

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
            denom = 1
            factors = []
            for j in range(n):
                if j == i or xs[i] == xs[j]:
                    continue
                denom += (xs[i] - xs[j])
                factors.append(xs[j])
            denom = MODULAR_INVERTER.modular_inverse(denom)
            term = RootsRepPoly(factors)
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
        return total % P

class Z_H:
    '''
    Represents the vanishing polynomial for the multiplicative subgroup
    contained within the finite field `F`.

    The polynomial Z() whose existence is asserted as part of step 3 is only specified to vanish
    over the Nth roots of unity, so we divide by the vanishing polynomial of the Nth roots
    to confirm Z()'s polynomialness.

    Z_H is public because it is specified wholly by N.
    '''
    def __init__(self):
        pass
    
    def evaluate(self, x):
        '''Computes Z_H(x).'''
        total = 1
        for k in range(N):
            total *= (x - (OMEGA**k))
        return total % P


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
        class R():
            # first, we implicitly extend A to A', which is A padded with elements from B
            # A = [a_1, a_2, ... a_N]
            # B = [b_1, b_2, ... b_n]
            # assume A', B are deduplicated
            def __init__(self, A, B):
                self.A = A
                self.B = B
                self.A_prime = A + [B[0]] * (N - len(A))
                assert len(self.A_prime) == N

                self.Z_B = RootsRepPoly(self.B)
                self.W_A = InverseRepPoly(self.A_prime) # remember A is padded here, so we use A prime
            
            def evaluate(self, x):
                Z_B_x = self.Z_B.evaluate(x)
                W_A_x = self.W_A.evaluate(x)
                return (Z_B_x * W_A_x) % P
        
        A = self.view['A']
        B = self.view['B']

        R = R(A, B)
        self.view['R'] = R
        self.view['Z_B'] = R.Z_B
        self.view['W_A'] = R.W_A

        A_poly = StandardRepPoly(A)
        self.view['A_poly'] = A_poly

        output = {'[A]_1': Commit(self.view['A_poly']), # slightly unfortunate notation calling both the set and polynom A
                  '[R]_1': Commit(self.view['R'])}
        self.view.update(**output)
        return output

    def step3(self):
        class Z():
            '''
            Represents the polynomial Z which is asserted to exist and have particular properties
            via a Grand Product Argument. Z satisfying these properties on the multiplicative subgroup
            will imply that W_A(gamma) = y.
            '''
            def __init__(self, gamma, W_A, Z_1 = 0):
                self.gamma = gamma
                self.W_A = W_A
                self.N = self.W_A.n # the order of the multiplicative subgroup Z is evaluated over; note A was padded to length N
                self.y = W_A.evaluate(self.gamma, self.N)
                self.Z_1 = Z_1 # the value that Z takes on at Z(1) = Z(omega^0) = Z(omega^N)
                self.omegas = [OMEGA**k for k in range(self.N)]
                self.evals = [self.z_omega(k) for k in range(self.N)]

                # we store the Lagrange Interpolation separately since
                # except for the challenge we evaluate only over the subgroup,
                # for which a simpler formula exists
                self.poly = LagrangeInterpolationPoly(self.omegas, self.evals)
            
            def z_omega(self, k):
                '''Evaluates Z(omega^k).'''
                term1 = self.y * MODULAR_INVERTER.modular_inverse(self.N) * k
                term2 = self.W_A.evaluate(self.gamma, k)
                return (self.Z_1 - term1 + term2) % P
            
            def evaluate(self, x):
                return self.poly.evaluate(x) % P

        class t():
            #  t(x) := \frac{1}{Z_H(X)} \left(\left(Z(\omega X) - Z(X) + \frac{y}{N}\right) \left(\gamma - A(X)\right) - 1\right)
            def __init__(self, Z, y, gamma, A_poly):
                self.Z_H = Z_H()
                self.Z = Z
                self.y = y
                self.gamma = gamma
                self.A_poly = A_poly
                self.N = self.Z.N

            def evaluate(self, x):
                denom = MODULAR_INVERTER.modular_inverse(self.Z_H.evaluate(x))
                term1 = self.Z.evaluate(OMEGA*x) - self.Z.evaluate(x) + (y * MODULAR_INVERTER.modular_inverse(N))
                term2 = gamma - self.A_poly.evaluate(x)
                return (denom * ((term1 * term2) - 1)) % P

        gamma = self.view['gamma']

        A_poly = self.view['A_poly']
        W_A = self.view['W_A']
        Z_B = self.view['Z_B']
        y = W_A.evaluate(gamma)

        self.view['Z'] = Z(gamma, W_A)
        self.view['t'] = t(self.view['Z'], y, gamma, A_poly)

        output = {'y': y,
                  'Z_B(gamma)': Z_B.evaluate(gamma),
                  '[Z]_1': Commit(self.view['Z']),
                  '[t]_1': Commit(self.view['t'])}
        self.view.update(**output)
        return output

    def step5(self):
        '''Prover collates all the information the Verifier needs to check the equality'''
        gamma = self.view['gamma']
        delta = self.view['delta']
        R = self.view['R']
        Z = self.view['Z']
        t = self.view['t']
        A_poly = self.view['A_poly']

        # I guess the prover could save this but they don't need to?
        output = {'R(gamma)': R.evaluate(gamma),
                  'Z(delta)': Z.evaluate(delta),
                  'Z(w*delta)': Z.evaluate(OMEGA*delta),
                  't(delta)': t.evaluate(delta),
                  'A_poly(delta)': A_poly.evaluate(delta)}
        self.view.update(**output)
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
        # check challenge one (step 2, called gamma)
        R_g = self.view['R(gamma)']
        Z_B_g = self.view['Z_B(gamma)']
        y = self.view['y']
        gamma_equality = (R_g == (Z_B_g * y) % P)

        # check challenge two (step 4, called delta)
        gamma = self.view['gamma']
        delta = self.view['delta']
        t_d = self.view['t(delta)']
        Z_H_d = Z_H().evaluate(delta)

        Z_wd = self.view['Z(w*delta)']
        Z_d = self.view['Z(delta)']
        A_d = self.view['A_poly(delta)']

        delta_equality_LHS = (t_d * Z_H_d) % P
        delta_equality_RHS = (Z_wd - Z_d + (y * MODULAR_INVERTER.modular_inverse(N)))
        delta_equality_RHS *= gamma - A_d
        delta_equality_RHS -= 1
        delta_equality_RHS = delta_equality_RHS % P
        delta_equality = (delta_equality_LHS == delta_equality_RHS)

        return 'accept' if gamma_equality and delta_equality else 'reject'

def main():
    # the premise is that A is private to the prover, but B is publicly known
    A = [1, 2, 7]
    B = [1, 2, 3, 7, 9]

    # routine assertions — otherwise the protocol doesn't apply as this isn't an accepting instance of the language
    assert N < P
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
