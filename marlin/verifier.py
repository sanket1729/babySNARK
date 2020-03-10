"""
The class to capture the state of the verifier in Marlin
"""

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix
from ssbls12 import Fp, Poly, Group
from babysnark import random_fp
from prover import vanishing_poly

"""
Get a random Fp outside of elements in domain
"""


def sample_fp_out_of_domain(domain):
    beta1 = random_fp()
    # Should not take long as domain_h <<< size of Fp
    while beta1 in domain:
        beta1 = random_fp()
    return beta1


class Verifier:
    def __init__(self, stmt_assignment, index_vk):
        self.stmt_assignment = stmt_assignment
        (
            self.row_poly_commit,
            self.col_poly_commit,
            self.val_poly_commit,
            self.pc,
            self.domain_h,
            self.domain_k,
            self.domain_x,
            self.domain_b,
        ) = index_vk

        self.PolyEvalRep_h = polynomialsEvalRep(
            Fp, self.domain_h[1], len(self.domain_h)
        )
        self.PolyEvalRep_x = polynomialsEvalRep(
            Fp, self.domain_x[1], len(self.domain_x)
        )
        self.PolyEvalRep_k = polynomialsEvalRep(
            Fp, self.domain_k[1], len(self.domain_k)
        )
        self.PolyEvalRep_b = polynomialsEvalRep(
            Fp, self.domain_b[1], len(self.domain_b)
        )

        # Precompute the representation of ONE
        omega2 = get_omega(Fp, 2 * len(self.domain_h), seed=0)
        self.PolyEvalRep_h2 = polynomialsEvalRep(Fp, omega2, 2 * len(self.domain_h))
        roots2 = [omega2 ** i for i in range(2 * len(self.domain_h))]
        # Saved as self.ONE to avoid recomputation
        # TODO: Maybe seperate parts from prover and precompute
        self.ONE = self.PolyEvalRep_h2(roots2, [Fp(1) for _ in roots2])

        # Precompute vanishing poly over H in PolyEvalRep form
        vanish_h = vanishing_poly(len(self.domain_h))
        self.vanish_h = self.PolyEvalRep_h2.from_coeffs(vanish_h)

        # Precompute vanishing poly over K in PolyEvalRep form over domain B
        vanish_k = vanishing_poly(len(self.domain_k))
        self.vanish_k = self.PolyEvalRep_b.from_coeffs(vanish_k)

        # Precompute vanishing poly over K in PolyEvalRep form
        vanish_h = vanishing_poly(len(self.domain_h))
        self.vanish_h = self.PolyEvalRep_h2.from_coeffs(vanish_h)

    def verifier_first_message(self):
        # Verifier only samples alpha and eta in the first round
        alpha = random_fp()
        self.alpha = alpha
        return alpha

    def verifier_second_message(self):
        beta1 = sample_fp_out_of_domain(self.domain_h)
        self.beta1 = beta1
        return beta1

    def verifier_third_message(self):
        beta2 = sample_fp_out_of_domain(self.domain_h)
        self.beta2 = beta2
        return beta2

    def verifier_fourth_message(self):
        beta3 = random_fp()
        self.beta3 = beta3
        return beta3

    # def verify_final_sumcheck_over_K(self, verifier_oracles_comms):
