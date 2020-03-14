"""
The class to capture the state of the verifier in Marlin
"""

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix, sparsePolynomialsOver
from ssbls12 import Fp, Poly, Group
from babysnark import random_fp
from prover import vanishing_poly
from indexer import eval_derivate_poly_diff_inputs

"""
Get a random Fp outside of elements in domain
"""

def sample_fp_out_of_domain(domain):
    beta1 = random_fp()
    # Should not take long as domain_h <<< size of Fp
    while beta1 in domain:
        beta1 = random_fp()
    return beta1

SparsePoly = sparsePolynomialsOver(Fp)
"""
Create a sparse Poly of the form x^n -1
"""
def sparse_vanishing_poly(n):
    return SparsePoly({0: Fp(-1), n: Fp(1)})

class Verifier:
    def __init__(self, index_vk):
        self.stmt_assignment = None
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

        self.PolyEvalRep_x = polynomialsEvalRep(
            Fp, self.domain_x[1], len(self.domain_x)
        )

        # Precompute vanishing poly over H in PolyEvalRep form
        self.sparse_vanish_h = sparse_vanishing_poly(len(self.domain_h))
        self.sparse_vanish_k = sparse_vanishing_poly(len(self.domain_k))
        self.sparse_vanish_x = sparse_vanishing_poly(len(self.domain_x))


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

    """
	Verify the proof for the claimed x according to the 
	indexed circuit
	"""

    def verify(self, x, proof):
        self.stmt_assignment = x
        poly_commits, poly_eval_proofs, sum_checks = proof

        sigma3, sigma2 = sum_checks

        all_poly_commits = (
            self.row_poly_commit,
            self.col_poly_commit,
            self.val_poly_commit,
        ) + poly_commits

        """
		All polycommits are proofs are properly indexed. 
		Loop over them and verify the evaluations
		"""
        for C, proof in zip(all_poly_commits, poly_eval_proofs):
            if not self.pc.verify_eval(C, proof):
                print("PolyCommit Check Failed")
                return False

        print("All Polynomial evaluations are correct")
        """
		Now all the evaluations are correct, check all sumchecks
		"""

        # Now that proofs are verified, throw away proofs and
        # only keep the evals
        evals = [proof[1] for proof in poly_eval_proofs]
        (
            row_eval_at_beta3,
            col_eval_at_beta3,
            val_eval_at_beta3,
            h3_eval_at_beta3,
            g3_eval_at_beta3,
            h2_eval_at_beta2,
            g2_eval_at_beta2,
            h1_eval_at_beta1,
            g1_eval_at_beta1,
            v_eval_at_beta1,
            w_eval_at_beta1,
            h0_eval_at_beta1,
        ) = evals

        """
		Check for A(beta2, beta1) over K: sigma3 Check
		"""
        v_h_at_beta1 = self.sparse_vanish_h(self.beta1)
        v_h_at_beta2 = self.sparse_vanish_h(self.beta2)

        lhs_t1 = v_h_at_beta2 * v_h_at_beta1 * val_eval_at_beta3
        lhs_t2 = (
            (self.beta2 - row_eval_at_beta3)
            * (self.beta1 - col_eval_at_beta3)
            * (self.beta3 * g3_eval_at_beta3 + sigma3 / Fp(len(self.domain_k)))
        )

        lhs = lhs_t1 - lhs_t2

        rhs = h3_eval_at_beta3 * self.sparse_vanish_k(self.beta3)

        if lhs != rhs:
            print("Inner Sumcheck for A(beta2, beta1) over K failed")
            return False
        else:
            print("Inner Sumcheck for A(beta2, beta1) over K successful")

        """
		Check the SumCheck over H for  r(alpha, X)*A(X, beta1)
		"""
        r_alpha_beta2 = eval_derivate_poly_diff_inputs(
            self.domain_h, self.alpha, self.beta2
        )
        lhs = r_alpha_beta2 * sigma3
        v_h_at_beta2 = self.sparse_vanish_h(self.beta2)

        rhs = (
            h2_eval_at_beta2 * v_h_at_beta2
            + self.beta2 * g2_eval_at_beta2
            + sigma2 / Fp(len(self.domain_h))
        )

        if lhs != rhs:
            print("Middle Sumcheck for r(alpha, X)*A(X, beta1) over H failed")
            return False
        else:
            print("Middle Sumcheck for r(alpha, X)*A(X, beta1) over H successful")

        """
        Check the SumCheck for r(alpha, X)*V(X) - sigma2*w(X) = h1(X)*vanish_h(X) + X*g2(X) at beta1
        """
        r_alpha_beta1 = eval_derivate_poly_diff_inputs(
            self.domain_h, self.alpha, self.beta1
        )

        # Compute the x_poly
        x_poly = self.PolyEvalRep_x(self.domain_x, self.stmt_assignment)
        self.x_poly = x_poly

        x_poly_at_beta1 = x_poly(self.beta1)
        v_x_at_beta1 = self.sparse_vanish_x(self.beta1)
        v_h_at_beta1 = self.sparse_vanish_h(self.beta1)

        """
        z and v are sometimes used interchanably. z is from marlin paper,
        and v is from SSP.
        use z(X) = w(X)*v_x(X) + x(X)
        """
        z_poly_at_beta1 = w_eval_at_beta1 * v_x_at_beta1 + x_poly_at_beta1

        lhs = r_alpha_beta1 * v_eval_at_beta1 - sigma2 * z_poly_at_beta1

        rhs = h1_eval_at_beta1 * v_h_at_beta1 + self.beta1 * g1_eval_at_beta1

        if lhs != rhs:
            print("Outer Sumcheck for r(alpha, X)*V(X) - sigma2*w(X) over H failed")
            return False
        else:
            print("Outer Sumcheck for r(alpha, X)*V(X) - sigma2*w(X) over H successful")

        """
        Final, RowCheck like babysnark
        """
        lhs = v_eval_at_beta1 ** 2 - Fp(1)  # v**2 -1
        rhs = h0_eval_at_beta1 * v_h_at_beta1  # h0*vh

        if lhs != rhs:
            print(
                "RowCheck for v(X)*v(X) - 1 = h0(X)*vanish_h(X) at beta1 over H failed"
            )
            return False
        else:
            print(
                "RowCheck for v(X)*v(X) - 1 = h0(X)*vanish_h(X) at beta1 over H successful"
            )

        print("All Checks passed, Verification Successful")
        return True
