from utils import *
import random

P = 101

class Prover:
    def __init__(self, A, B, C):
        self.view = {}  # represents the "view" of the Prover: all information visible to them during the interactive protocol
        self.view['A'] = A
        self.view['B'] = B
        self.view['B'] = C

    def receive(self, message):
        '''
        Records a message sent by the Verifier.

        `message`: a dictionary of strings to values representing the contents of a message
        in the interactive protocol
        '''
        self.view.update(**message)

    def step1_compute_poly(self):
        '''
        Given multisets A, B, C, computes z_A, z_B, z_C
        Then compute c_A, c_B, P, Q from z_A, z_B, z_C so that it satisfies the following

        z_C * c_A = z_A
        z_C * c_B = z_B
        P * z_A + Q * z_B = z_C

        P and Q can be found from extended Euclidean Algo

        Prover sends commitments of z_A, z_B, z_C, c_A, c_B, P, Q
        '''
        z_A = RootsRepPoly(self.view['A'])
        z_B = RootsRepPoly(self.view['B'])
        z_C = RootsRepPoly(self.view['C'])

        P, Q = self.euclidean_algo(z_A, z_B, z_C)

        c_A = RootsRepPoly(list(set(z_C.roots).difference(set(z_A.roots))))
        c_B = RootsRepPoly(list(set(z_C.roots).difference(set(z_B.roots))))

        output = {
            'z_A': Commit(z_A),
            'z_B': Commit(z_B),
            'z_C': Commit(z_C),
            'P': Commit(P),
            'Q': Commit(Q),
            'c_A': Commit(c_A),
            'c_B': Commit(c_B)
        }

        self.view.update(**output)

        return output

    def euclidean_algo(self, z_A, z_B, z_C):
        '''
        implementation of extended gcd algorithm to find P, Q

        (currently unimplemented - we assume this works)
        '''

        P = RootsRepPoly([])
        Q = RootsRepPoly([])

        return P, Q

    def step3_eval_poly(self):
        '''
        prover receives random point gamma, computes the following
        z_A(gamma), z_B(gamma), z_C(gamma), c_A(gamma), c_B(gamma), P(gamma), Q(gamma)
        and send it back to the verifier

        '''
        gamma = self.view['gamma']
        z_A = self.view['z_A'].open()
        z_B = self.view['z_B'].open()
        z_C = self.view['z_C'].open()
        c_A = self.view['c_A'].open()
        c_B = self.view['c_B'].open()
        P = self.view['P'].open()
        Q = self.view['Q'].open()

        output = {
            'z_A(gamma)': z_A.evaluate(gamma),
            'z_B(gamma)': z_B.evaluate(gamma),
            'z_C(gamma)': z_C.evaluate(gamma),
            'P(gamma)': P.evaluate(gamma),
            'Q(gamma)': Q.evaluate(gamma),
            'c_A(gamma)': c_A.evaluate(gamma),
            'c_B(gamma)': c_B.evaluate(gamma)
        }
        return output


class Verifier:
    def __init__(self):
        self.view = {}  # represents the "view" of the Verifier: all information visible to them during the interactive protocol

    def receive(self, message):
        '''
        Records a message sent by the Prover.

        `message`: a dictionary of strings to values representing the contents of a message
        in the interactive protocol
        '''
        self.view.update(**message)

    def step2_generate_random_pt(self):
        '''
        verifier sends over a random point in field F
        '''
        gamma = random.randint(0, P)
        self.view['gamma'] = gamma
        return gamma

    def step4_intersection_check(self):
        '''
        checks that A \cap B = C
        z_A, z_B, z_C, c_A, c_B, P, Q are polynomials in standard representation

        gamma is a point randomly picked in field F

        z_A, z_B, z_C are polynomials representing multisets A, B, and C in roots form
        P, Q are polynomials constructed from Bezout's Thm, to show that C is a superset of A \cap B
        c_A, c_B are polynomials constructed to show that C is subset of A \cap B


        If we can show that the following holds for the set of polynomials {z_A, z_B, z_C, c_A, c_B, P, Q},
        then A \cap B = C

        z_C * c_A = z_A
        z_C * c_B = z_B
        P * z_A + Q * z_B = z_C
        '''

        z_A_gamma = self.view['z_A(gamma)']
        z_B_gamma = self.view['z_B(gamma)']
        z_C_gamma = self.view['z_B(gamma)']
        c_A_gamma = self.view['c_A(gamma)']
        c_B_gamma = self.view['c_B(gamma)']
        P_gamma = self.view['P(gamma)']
        Q_gamma = self.view['Q(gamma)']

        assert z_C_gamma * c_A_gamma == z_A_gamma
        assert z_C_gamma * c_B_gamma == z_B_gamma
        assert P_gamma * z_A_gamma + Q_gamma * z_B_gamma == z_C_gamma


def main():



# if __name__ == "__main__":

