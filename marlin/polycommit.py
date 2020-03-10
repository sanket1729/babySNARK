"""
Minimal class for polycommit
"""
import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))

from ssbls12 import Fp, Poly, Group
from babysnark import evaluate_in_exponent, random_fp

G = Group.G
GT = Group.GT


"""
Note that the notation is not consistent with the paper.
The public key is already assumed to be initilized in the scheme.

There are other features which are not implemented because of the 
minial requirement
"""


class PolyCommit:
    def __init__(self, max_degree=0, crs=None):
        if crs is None:
            # If CRS is not given, there must a degree bound given
            assert max_degree > 0
            tau = random_fp()
            crs = [G * (tau ** i) for i in range(max_degree + 1)]
        self.crs = crs
        self.max_degree = len(crs)

    def commit(self, poly):
        # poly:
        #    degree-bound polynomial in coefficient form
        assert poly.degree() + 1 < self.max_degree
        return sum(
            [self.crs[i] * poly.coefficients[i] for i in range(poly.degree() + 1)],
            G * 0,
        )

    """
    Create witness
    """

    def create_witness(self, poly, i):

        val = poly(i)
        x_minus_i = Poly([Fp(-i), Fp(1)])
        psi = (poly - Poly([Fp(val)])) / x_minus_i
        # Committing and evaluating in exponent are the same thing
        witness = self.commit(psi)

        assert poly == psi * x_minus_i + Poly([Fp(val)])
        proof = i, val, witness
        return proof

    """
    Veryify that the commited polynomial under polycommit indeed 
    evaluates to correct value val at evaluation point i
    """

    def verify_eval(self, polycommit, proof):
        i, val, witness = proof
        lhs = polycommit.pair(G)
        rhs = (witness.pair(self.crs[1] - G * i)) * (G.pair(G * val))

        return lhs == rhs


# TODO: Convert to test
if __name__ == "__main__":
    f = Poly([Fp(1), Fp(4), Fp(2), Fp(3)])
    pc = PolyCommit(max_degree=5)
    C = pc.commit(f)
    i = Fp(10)
    proof = pc.create_witness(f, i)

    assert pc.verify_eval(C, proof)
