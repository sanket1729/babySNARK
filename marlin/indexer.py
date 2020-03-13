"""
The indexer offline phase of the marlin protocol. In this phase we will
preprocess a circuit into resptive polynomials using AHP.
"""
import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))
from ssbls12 import Fp, Poly, Group
from util import isPowerOfTwo, nearestPowerOfTwo
from operator import mul
from itertools import accumulate
from circuit import BooleanCircuit
from babysnark import evaluate_in_exponent

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix


"""
Evaluate the derivate polynomial of domain at x
u_S(X, X) = |S|*X**(|S|−1)
requires only log(|S|) time to evaluate.
"""


def eval_derivate_poly(domain, x):
    assert type(x) is Fp
    return Fp(len(domain)) * x ** (len(domain) - 1)


"""
Evaluate the derivate polynomial of domain at x
u_S(X, X) = |S|*X**(|S|−1)
requires only log(|S|) time to evaluate.
"""


def eval_derivate_poly_diff_inputs(domain, x, y):
    assert type(x) is Fp and type(y) is Fp
    assert x != y
    num = x ** len(domain) - y ** len(domain)
    denom = x - y
    return num / denom


"""
Offline Indexer for Marlin
"""


class Indexer:
    def __init__(self, circuit, pc):
        self.pc = pc
        # The circuit here is already of the required format
        # The dirmension is adjusted to be 2^k for some k by adding
        # dummy constraints as square matrix is required where both
        # dimensions are some power of 2
        self.n_stmt, self.U = circuit.compile_to_unsolved_ssp(make_square=True)

        self.n_witness = self.U.n - self.n_stmt

        # check both dimensions respect the power of two
        assert isPowerOfTwo(self.U.m) and isPowerOfTwo(self.U.n)
        # U must be a square
        assert self.U.m == self.U.n

    """
	Get the evaluation domains corresponding to num_elems in a 
	multiplicative subgroup. 
	"""

    def get_evaluation_domain(self, num_elems):
        num_elems = nearestPowerOfTwo(num_elems)
        omega = get_omega(Fp, num_elems, seed=0)
        domain = list(accumulate([omega ** 0] + [omega] * (num_elems - 1), mul))

        assert len(domain) == num_elems and isPowerOfTwo(len(domain))
        return domain

    """
	Convert the matrix into polynomials using low degree extensions.
	This is the AHP part of marlin.
	"""

    def matrix_to_polys(self, domain_k, domain_h, domain_x, domain_b):
        row_vec = []
        col_vec = []
        val_vec = []

        count = 0
        for i, rowdict in enumerate(self.U.rows()):
            row_val = domain_h[i]
            for index in sorted(rowdict.keys()):
                col_val = domain_h[reindex_by_subdomain(index, domain_h, domain_x)]
                val = rowdict[index]
                row_vec.append(row_val)
                col_vec.append(col_val)
                val = val / (
                    eval_derivate_poly(domain_h, row_val)
                    * eval_derivate_poly(domain_h, col_val)
                )
                val_vec.append(val)
                count += 1

        """
		Add in the remaining indices to make it a power of two
		"""
        while count < len(domain_k):
            row_vec.append(domain_h[0])
            col_vec.append(domain_h[0])
            val_vec.append(Fp(0))
            count += 1

        # Now row_vec represents the evaluations of domain_k
        PolyEvalRep_k = polynomialsEvalRep(Fp, domain_k[1], len(domain_k))
        row_poly = PolyEvalRep_k(domain_k, row_vec)
        col_poly = PolyEvalRep_k(domain_k, col_vec)
        val_poly = PolyEvalRep_k(domain_k, val_vec)

        # print(row_poly)
        return (
            row_poly.to_coeffs(),
            col_poly.to_coeffs(),
            val_poly.to_coeffs(),
            row_poly,
            col_poly,
            val_poly,
        )

    """
	Index a circuit
	"""

    def index(self):

        # Domain here refers to the powers of omega for fft operations
        # We stick to the paper in denoting the domains.

        # Represents the interpolation domain
        domain_h = self.get_evaluation_domain(self.U.n)
        # Represents the output domain
        domain_k = self.get_evaluation_domain(self.U.num_non_zero_elems())
        # Represents the input domain
        domain_x = self.get_evaluation_domain(self.n_stmt)
        # Represents the expanded domain: For polycommit optimization
        domain_b = self.get_evaluation_domain(6 * len(domain_k) - 6)

        (
            row_poly,
            col_poly,
            val_poly,
            row_poly_evals,
            col_poly_evals,
            val_poly_evals,
        ) = self.matrix_to_polys(domain_k, domain_h, domain_x, domain_b)

        # Create commitments
        row_poly_commit = self.pc.commit(row_poly)
        col_poly_commit = self.pc.commit(col_poly)
        val_poly_commit = self.pc.commit(val_poly)

        # Indexer verification key
        indexer_vk = (
            row_poly_commit,
            col_poly_commit,
            val_poly_commit,
            self.pc,
            domain_h,
            domain_k,
            domain_x,
            domain_b,
        )
        # Indexer public key
        self.row_poly = row_poly
        self.col_poly = col_poly
        self.val_poly = val_poly
        indexer_pk = (
            self.U,
            row_poly,
            col_poly,
            val_poly,
            row_poly_evals,
            col_poly_evals,
            val_poly_evals,
            self.pc,
            domain_h,
            domain_k,
            domain_x,
            domain_b,
        )

        return indexer_pk, indexer_vk


"""
Given an index which assumes the first elements of 
this domain are the elements of another (sub)domain 
with size size_s, this returns the actual index into 
this domain.
"""


def reindex_by_subdomain(index, domain_h, domain_x):
    period = len(domain_h) // len(domain_x)
    assert len(domain_h) % len(domain_x) == 0
    if index < len(domain_x):
        return index * period
    else:
        # TODO: Add calculation explaination here
        i = index - len(domain_x)
        x = period - 1
        return i + (i // x) + 1
