"""
The class to capture the state of the prover after various 
invocations of the oracles.
"""

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix
from ssbls12 import Fp, Poly, Group

def vanishing_poly(omega, n):
    # For the special case of evaluating at all n powers of omega,
    # the vanishing poly has a special form.
    #  t(X) = (X-1)(X-omega)....(X-omega^(n-1)) = X^n - 1
    return Poly([Fp(-1)] + [Fp(0)] * (n - 1) + [Fp(1)])

class Prover:
	def __init__(self, stmt_assignment, witness_assignment, index_pk, index_vk):
		# Mapping from statement wires to
		# correponding inputs by prover
		self.stmt_assignment = stmt_assignment
		# Witness assignment
		self.witness_assignment = witness_assignment
		# Full a vector
		self.a = self.stmt_assignment + self.witness_assignment
		(
			self.U,
			self.row_poly,
			self.col_poly,
			self.val_poly,
			self.pc_verifier_key,
			self.pc_commiter_key,
			self.domain_h,
			self.domain_k,
			self.domain_x,
			self.domain_b,
		) = index_pk

	def first_round_prover(self):
		# In the first round, prover needs to commit
		# to the oracle U*a

		# First compute v, similar to babysnark
		PolyEvalRep_h = polynomialsEvalRep(Fp, self.domain_h[1], len(self.domain_h))
		v_poly = PolyEvalRep_h((), ())
		for (i, k), y in self.U.items():
			x = self.domain_h[i]
			v_poly += PolyEvalRep_h([x], [y]) * self.a[k]

		# Compute the x_poly and witness poly
		# assume statements are power of 2.
		PolyEvalRep_x = polynomialsEvalRep(Fp, self.domain_x[1], len(self.domain_x))
		x_poly = PolyEvalRep_x(self.domain_x, self.stmt_assignment)

		# Store the evaluations of x_poly on self.domain_h
		x_evals_on_h = PolyEvalRep_h.from_coeffs(x_poly.to_coeffs())

		# Compute the witness_poly from witness assignment
		period = len(self.domain_h) // len(self.domain_x)
		assert len(self.domain_h) % len(self.domain_x) == 0
		"""
		w_poly_evals is divided such that statements also form a multiplicative
		subgroup. for s0, s1, s2, s3 statements, and w_i as the witness
		w_poly_evals = [s0 w0 w1.... s1 ..... s2.....s3]
		such that s0, s1, s2 and s3 also form a multiplicative subgroup
		of group H.

		"""
		w_poly_evals = []
		for i in range(len(self.domain_h)):
			if i % period == 0:
				w_poly_evals.append(Fp(0))
			else:
				val = self.witness_assignment[i - i//period - 1]  - x_evals_on_h.evalmap[self.domain_h[i]]
				w_poly_evals.append(val)


		a_full_poly = PolyEvalRep_h(self.domain_h, w_poly_evals)

		# This must be divisble vanishing polynomial over domain_x
		# because of our construction.
		x_vanishing_poly = vanishing_poly(omega = self.domain_x[1], n = len(self.domain_x))
		w_poly = PolyEvalRep_h.divideWithCoset(a_full_poly.to_coeffs(), x_vanishing_poly)

		assert w_poly * x_vanishing_poly == a_full_poly.to_coeffs()

		first_round_prover_oracles = (w_poly, v_poly)

		return first_round_prover_oracles
