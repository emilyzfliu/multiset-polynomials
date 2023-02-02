from utils import *
import itertools

def poly_root_form_to_coef_form(roots):
    '''
    roots is a list of roots or polynomial in the form of
    (x-r_1)(x-r_2)...(x-r_n)

    the function converts a list of roots into a list of coefficients, in the form of
    [c_n, c_{n-1}, ..., c_0], where the coefficients are from
    c_n x^n + c_{n-1} x^{n-1} + ... + c_0

    used algorithm from
    https://cs.stackexchange.com/questions/98107/calculating-a-polynomials-coefficients-from-its-roots
    '''
    i = len(roots)
    if i == 1:
        return [1, -1 * roots[0]]
    else:
        coef_i_m_1 = poly_root_form_to_coef_form(roots[:i-1])
        coef_i = []
        last_root = roots[i-1]
        for k in range(i-1):
            coef_i.append(-1 * coef_i_m_1[k] * last_root + coef_i_m_1[k+1])
        coef_i.append(-1 * coef_i_m_1[i-1] * last_root)
        coef_i = [1] + coef_i # add leading coefficient 1
        return coef_i

def poly_mul(A, B):
    '''
    A, B are two polynomials in coefficient form
    return the result of polynomial multiplication in coef form

    adapted from https://stackoverflow.com/questions/5413158/multiplying-polynomials-in-python
    '''
    res = [0] * (len(A) + len(B) - 1)
    for selfpow, selfco in enumerate(A):
        for valpow, valco in enumerate(B):
            res[selfpow + valpow] += selfco * valco
    return res

def poly_add(A, B):
    '''
    A, B are two polynomials in coefficient form
    return the result of polynomial addition in coef form

    adapted from https://stackoverflow.com/questions/5413158/multiplying-polynomials-in-python
    '''
    res = [a+b for a,b in itertools.zip_longest(reversed(A), reversed(B), fillvalue=0)]
    res.reverse()
    return res
def intersection_check(z_A, z_B, z_C, c_A, c_B, P, Q):
    '''
    If we can show that the following holds, then A \cap B = C
    z_C * c_A = z_A
    z_C * c_B = z_B
    P * z_A + Q * z_B = z_C

    z_A, z_B, z_C, c_A, c_B in roots form
    P, Q in coefficient form
    '''
    assert sorted(z_C + c_A) == sorted(z_A)
    assert sorted(z_C + c_B) == sorted(z_B)

    z_A_coef = poly_root_form_to_coef_form(z_A)
    z_B_coef = poly_root_form_to_coef_form(z_B)
    z_C_coef = poly_root_form_to_coef_form(z_C)
    assert poly_add(poly_mul(P, z_A_coef), poly_mul(Q, z_B_coef)) == z_C_coef


# if __name__ == "__main__":

