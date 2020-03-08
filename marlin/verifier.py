"""
The class to capture the state of the verifier in Marlin
"""

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix
from ssbls12 import Fp, Poly, Group
from babysnark import random_fp

class Verifier:

	def __init__(self, stmt_assignment, index_vk):
		self.stmt_assignment = stmt_assignment
		(
			self.row_poly_commit,
			self.col_poly_commit,
			self.val_poly_commit,
			self.pc_verifier_key,
			self.domain_h,
			self.domain_k,
			self.domain_x,
			self.domain_b,
		) = index_vk

	def verifier_first_message(self):
		# Verifier only samples alpha and eta in the first round
		alpha = random_fp()
		eta = random_fp()

		return alpha, eta