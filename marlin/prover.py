"""
The class to capture the state of the prover after various 
invocations of the oracles.
"""

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix
from ssbls12 import Fp, Poly, Group
from indexer import eval_derivate_poly


def vanishing_poly(n):
    # For the special case of evaluating at all n powers of omega,
    # the vanishing poly has a special form.
    #  t(X) = (X-1)(X-omega)....(X-omega^(n-1)) = X^n - 1
    return Poly([Fp(-1)] + [Fp(0)] * (n - 1) + [Fp(1)])


"""
Evaluate a vanishing poly over domain `domain` at val
TODO:
"""


def eval_vanishing_poly(domain, val):
    pass


class Prover:
    def __init__(self, index_pk, index_vk):
        self.stmt_assignment = None
        # Witness assignment
        self.witness_assignment = None
        # Full a vector
        self.a = None
        # Parse index_pk
        (
            self.U,
            self.row_poly,
            self.col_poly,
            self.val_poly,
            self.row_poly_evals,
            self.col_poly_evals,
            self.val_poly_evals,
            self.pc,
            self.domain_h,
            self.domain_k,
            self.domain_x,
            self.domain_b,
        ) = index_pk

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

        # Precompute vanish_x over H
        vanish_x = vanishing_poly(n=len(self.domain_x))
        self.vanish_x = self.PolyEvalRep_h.from_coeffs(vanish_x)

    def first_round_prover(self):
        # In the first round, prover needs to commit
        # to the oracle U*a

        # First compute v,h similar to babysnark
        v_poly = self.PolyEvalRep_h((), ())
        for (i, k), y in self.U.items():
            x = self.domain_h[i]
            v_poly += self.PolyEvalRep_h([x], [y]) * self.a[k]

        self.v_poly = v_poly
        v2 = self.PolyEvalRep_h2.from_coeffs(v_poly.to_coeffs())

        p2 = v2 * v2 - self.ONE
        p = p2.to_coeffs()

        # Find the polynomial h_0 by dividing p / vanishing poly
        t = self.vanish_h.to_coeffs()
        h0_poly = self.PolyEvalRep_h2.divideWithCoset(p, t)
        assert h0_poly * t == p
        self.h0_poly = self.PolyEvalRep_h2.from_coeffs(h0_poly)
        # Compute the x_poly and witness poly
        # assume statements are power of 2.
        x_poly = self.PolyEvalRep_x(self.domain_x, self.stmt_assignment)
        self.x_poly = x_poly
        # Store the evaluations of x_poly on self.domain_h
        x_evals_on_h = self.PolyEvalRep_h.from_coeffs(x_poly.to_coeffs())

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
                val = (
                    self.witness_assignment[i - i // period - 1]
                    - x_evals_on_h.evalmap[self.domain_h[i]]
                )
                w_poly_evals.append(val)

        a_full_poly = self.PolyEvalRep_h(self.domain_h, w_poly_evals)

        # This must be divisble vanishing polynomial over domain_x
        # because of our construction.
        x_vanishing_poly = self.vanish_x.to_coeffs()
        w_poly = self.PolyEvalRep_h.divideWithCoset(
            a_full_poly.to_coeffs(), x_vanishing_poly
        )

        assert w_poly * x_vanishing_poly == a_full_poly.to_coeffs()
        self.w_poly = self.PolyEvalRep_h.from_coeffs(w_poly)

        """
		Return everything in coeff form
		"""
        first_round_prover_oracles = (w_poly, v_poly.to_coeffs(), h0_poly)

        return first_round_prover_oracles

    def precomp_derivate_poly_values(self):
        precomp = {}
        for elem in self.domain_h:
            precomp[elem] = eval_derivate_poly(self.domain_h, elem)

        return precomp

    def prover_second_round(self, alpha):

        # First, get the r(alpha, x) poly
        r_alpha_evals_on_h = []
        vanish_alpha = self.vanish_h(alpha)
        for i in range(len(self.domain_h)):
            r_alpha_evals_on_h.append(vanish_alpha / (alpha - self.domain_h[i]))

        self.r_alpha_poly = self.PolyEvalRep_h(self.domain_h, r_alpha_evals_on_h)

        # Now get the Rm(alpha, X)
        r_a_alpha_vals_on_H = {}
        derivate_poly_values = self.precomp_derivate_poly_values()
        for k in range(len(self.domain_k)):
            row_at_k = self.row_poly_evals.evalmap[self.domain_k[k]]
            col_at_k = self.col_poly_evals.evalmap[self.domain_k[k]]
            val_at_k = self.val_poly_evals.evalmap[self.domain_k[k]]
            prod = (
                derivate_poly_values[row_at_k]
                * derivate_poly_values[col_at_k]
                * val_at_k
                * self.r_alpha_poly.evalmap[row_at_k]
            )
            r_a_alpha_vals_on_H[col_at_k] = (
                r_a_alpha_vals_on_H.get(col_at_k, Fp(0)) + prod
            )

        self.r_a_alpha_poly = self.PolyEvalRep_h(
            r_a_alpha_vals_on_H.keys(), r_a_alpha_vals_on_H.values()
        )

        # Compute the complete z(used interchaning with a) poly

        x_vanishing_poly = vanishing_poly(n=len(self.domain_x))
        x_vanishing_poly = self.PolyEvalRep_h2.from_coeffs(x_vanishing_poly)
        w2 = self.PolyEvalRep_h2.from_coeffs(self.w_poly.to_coeffs())
        self.z_poly = w2 * x_vanishing_poly

        # assert self.z_poly.to_coeffs() == w2.to_coeffs() * x_vanishing_poly.to_coeffs()

        # print(self.z_poly.to_coeffs().degree(), "z Degree")
        # print(w2.to_coeffs().degree(), "w2 Degree")
        # print(x_vanishing_poly.to_coeffs().degree(), "x_vanishing_poly Degree")
        x2 = self.PolyEvalRep_h2.from_coeffs(self.x_poly.to_coeffs())
        self.z_poly = self.z_poly + x2

        # Finally compute the product: r(a,X)*v - r_a(a,X)*z
        # Change representations, don't need for z_poly as it is already correct
        r_h2 = self.PolyEvalRep_h2.from_coeffs(self.r_alpha_poly.to_coeffs())
        v_h2 = self.PolyEvalRep_h2.from_coeffs(self.v_poly.to_coeffs())
        r_a_h2 = self.PolyEvalRep_h2.from_coeffs(self.r_a_alpha_poly.to_coeffs())

        # Calculate q
        self.q1 = (r_h2 * v_h2) - (r_a_h2 * self.z_poly)
        # print(self.q1.to_coeffs().degree(), "q1 Degree")
        # print(len(self.domain_h), "DOmain H len")

        # TODO: This is n**2, need to implement nlog(n)
        h1, g1_x = divmod(self.q1.to_coeffs(), self.vanish_h.to_coeffs())

        # The constant term of g1_x must be zero
        assert g1_x.coefficients[0] == Fp(0)

        # Obtain g1 by dividing by x
        g1 = g1_x / Poly([Fp(0), Fp(1)])

        second_round_oracles = (h1, g1)
        self.g1 = self.PolyEvalRep_h2.from_coeffs(g1)
        self.h1 = self.PolyEvalRep_h2.from_coeffs(h1)

        return second_round_oracles

    def prover_third_round(self, alpha, beta1):

        # First, get the r(beta1, x) poly
        r_beta1_evals_on_h = []
        vanish_beta1 = self.vanish_h(beta1)
        for i in range(len(self.domain_h)):
            r_beta1_evals_on_h.append(vanish_beta1 / (beta1 - self.domain_h[i]))

        self.r_beta1_poly = self.PolyEvalRep_h(self.domain_h, r_beta1_evals_on_h)

        """
		Compute the polynomial M(X, beta1)
		"""
        r_a_beta1_vals_on_H = {}
        derivate_poly_values = self.precomp_derivate_poly_values()
        for k in range(len(self.domain_k)):
            row_at_k = self.row_poly_evals.evalmap[self.domain_k[k]]
            col_at_k = self.col_poly_evals.evalmap[self.domain_k[k]]
            val_at_k = self.val_poly_evals.evalmap[self.domain_k[k]]
            prod = (
                derivate_poly_values[row_at_k]
                * val_at_k
                * self.r_beta1_poly.evalmap[col_at_k]
            )
            r_a_beta1_vals_on_H[row_at_k] = (
                r_a_beta1_vals_on_H.get(row_at_k, Fp(0)) + prod
            )

        self.r_a_beta1_poly = self.PolyEvalRep_h(
            r_a_beta1_vals_on_H.keys(), r_a_beta1_vals_on_H.values()
        )

        """
		Similar to previous case, convert the polys to higher rep
		"""
        r_alpha_h2 = self.PolyEvalRep_h2.from_coeffs(self.r_alpha_poly.to_coeffs())
        r_a_beta_h2 = self.PolyEvalRep_h2.from_coeffs(self.r_a_beta1_poly.to_coeffs())

        self.q2 = r_alpha_h2 * r_a_beta_h2

        # TODO: This is n**2, need to implement nlog(n)
        h2, g2_x_plus_sigma2 = divmod(self.q2.to_coeffs(), self.vanish_h.to_coeffs())

        sigma2 = len(self.domain_h) * g2_x_plus_sigma2.coefficients[0]
        g2 = Poly(g2_x_plus_sigma2.coefficients[1:])

        self.g2 = self.PolyEvalRep_h2.from_coeffs(g2)
        self.h2 = self.PolyEvalRep_h2.from_coeffs(h2)

        third_round_oracles = (h2, g2)

        assert g2.degree() <= len(self.domain_h) - 2
        assert h2.degree() <= len(self.domain_h) - 2

        return third_round_oracles, sigma2

    def prover_fourth_round(self, aplha, beta1, beta2):

        vanish_poly_at_beta1 = self.vanish_h(beta1)
        vanish_poly_at_beta2 = self.vanish_h(beta2)

        f3_evals_on_K = []
        sigma3 = Fp(0)
        for k in range(len(self.domain_k)):
            row_at_k = self.row_poly_evals.evalmap[self.domain_k[k]]
            col_at_k = self.col_poly_evals.evalmap[self.domain_k[k]]
            val_at_k = self.val_poly_evals.evalmap[self.domain_k[k]]

            denominator = (beta2 - row_at_k) * (beta1 - col_at_k)
            f3_eval_at_k = (
                vanish_poly_at_beta1 * vanish_poly_at_beta2 * val_at_k / denominator
            )

            f3_evals_on_K.append(f3_eval_at_k)
            sigma3 = sigma3 + f3_eval_at_k

        self.f3_poly = self.PolyEvalRep_k(self.domain_k, f3_evals_on_K)

        g3 = Poly(self.f3_poly.to_coeffs().coefficients[1:])

        self.g3_poly = self.PolyEvalRep_k.from_coeffs(g3)

        assert self.f3_poly.to_coeffs() == Poly(
            [Fp(0), Fp(1)]
        ) * self.g3_poly.to_coeffs() + sigma3 / Fp(len(self.domain_k))

        """
		Compute the polys a and b
		"""
        val_poly_at_B = self.PolyEvalRep_b.from_coeffs(self.val_poly)
        row_poly_at_B = self.PolyEvalRep_b.from_coeffs(self.row_poly)
        col_poly_at_B = self.PolyEvalRep_b.from_coeffs(self.col_poly)
        a_poly_evals_at_B = []
        b_poly_evals_at_B = []
        for b in range(len(self.domain_b)):
            row_at_b = row_poly_at_B.evalmap[self.domain_b[b]]
            col_at_b = col_poly_at_B.evalmap[self.domain_b[b]]
            try:
                val_at_b = val_poly_at_B.evalmap[self.domain_b[b]]
            except KeyError:
                val_at_b = Fp(0)

            eval_a = vanish_poly_at_beta1 * vanish_poly_at_beta2 * val_at_b
            a_poly_evals_at_B.append(eval_a)

            eval_beta2 = beta2 - row_at_b
            eval_beta1 = beta1 - col_at_b
            b_poly_evals_at_B.append(eval_beta1 * eval_beta2)

        self.a_poly = self.PolyEvalRep_b(self.domain_b, a_poly_evals_at_B)
        self.b_poly = self.PolyEvalRep_b(self.domain_b, b_poly_evals_at_B)

        # Compute sumcheck poly

        f3_over_B_poly = self.PolyEvalRep_b.from_coeffs(self.f3_poly.to_coeffs())
        lhs = self.a_poly - (self.b_poly * f3_over_B_poly)
        h3 = self.PolyEvalRep_b.divideWithCoset(
            lhs.to_coeffs(), self.vanish_k.to_coeffs()
        )

        self.h3 = self.PolyEvalRep_b.from_coeffs(h3)
        assert self.h3.to_coeffs() * self.vanish_k.to_coeffs() == lhs.to_coeffs()

        fourth_round_oracles = h3, g3

        return fourth_round_oracles, sigma3

    def prove(self, x, w, verifier):
        # Mapping from statement wires to
        # correponding inputs by prover
        self.stmt_assignment = x
        # Witness assignment
        self.witness_assignment = w
        # Full a vector
        self.a = self.stmt_assignment + self.witness_assignment
        """
		Get the prover oracles for the first round, the orcales in this 
		case are (v_poly and w_poly) representing U*a and a repectively
		"""
        first_round_oracles = self.first_round_prover()

        # Commit to the prover first round oracles
        (w_poly, v_poly, h0_poly) = first_round_oracles
        w_poly_commit = self.pc.commit(w_poly)
        v_poly_commit = self.pc.commit(v_poly)
        h0_poly_commit = self.pc.commit(h0_poly)

        # Get the verifier challenges alpha and eta
        alpha = verifier.verifier_first_message()

        second_round_oracles = self.prover_second_round(alpha)

        (h1_poly, g1_poly) = second_round_oracles

        h1_poly_commit = self.pc.commit(h1_poly)
        g1_poly_commit = self.pc.commit(g1_poly)

        beta1 = verifier.verifier_second_message()

        third_round_oracles, sigma2 = self.prover_third_round(alpha, beta1)

        h2_poly, g2_poly = third_round_oracles

        h2_poly_commit = self.pc.commit(h2_poly)
        g2_poly_commit = self.pc.commit(g2_poly)

        beta2 = verifier.verifier_third_message()

        fourth_round_oracles, sigma3 = self.prover_fourth_round(alpha, beta1, beta2)

        h3_poly, g3_poly = fourth_round_oracles

        h3_poly_commit = self.pc.commit(h3_poly)
        g3_poly_commit = self.pc.commit(g3_poly)

        beta3 = verifier.verifier_fourth_message()

        """
		h3(X)*vanish_k(X) = a(X) - b(X)*(X*G(X) + sigma3/|K|) at beta3
		In the equation, needs to give oracle proofs for row, col, val, 
		h and g at beta3
		"""
        h3_eval_at_beta3_proof = self.pc.create_witness(h3_poly, beta3)
        g3_eval_at_beta3_proof = self.pc.create_witness(g3_poly, beta3)
        row_eval_at_beta3_proof = self.pc.create_witness(self.row_poly, beta3)
        col_eval_at_beta3_proof = self.pc.create_witness(self.col_poly, beta3)
        val_eval_at_beta3_proof = self.pc.create_witness(self.val_poly, beta3)

        """
		r(alpa, X)*sigma3 = h2(X)*vanish_h(X) + X*g2(X) + sigma2/|H| at beta2
		Again, the verifier can get other terms all by himself, he only
		needs oracle access to h2 and g2 with eval proofs
		"""
        h2_eval_at_beta2_proof = self.pc.create_witness(h2_poly, beta2)
        g2_eval_at_beta2_proof = self.pc.create_witness(g2_poly, beta2)

        """
		r(alpa, X)*V(X) - sigma2*w(X) = h1(X)*vanish_h(X) + X*g2(X) at beta1
		Again, the verifier can get other terms all by himself, he only
		needs oracle access to v, w, h1 and g1 with eval proofs
		The verifier will extend w with this public input
		to make sure that statements is indeed satisfied.
		"""
        h1_eval_at_beta1_proof = self.pc.create_witness(h1_poly, beta1)
        g1_eval_at_beta1_proof = self.pc.create_witness(g1_poly, beta1)
        v_eval_at_beta1_proof = self.pc.create_witness(v_poly, beta1)
        w_eval_at_beta1_proof = self.pc.create_witness(w_poly, beta1)

        """
		The final rowcheck which is similar to babysnark, checking
		whether v(X)*v(X) - 1 = h0(X)*vanish_h(X) at beta1.
		We only need value of h0(X) at beta1
		"""
        h0_eval_at_beta1_proof = self.pc.create_witness(h0_poly, beta1)

        poly_eval_proofs = (
            row_eval_at_beta3_proof,
            col_eval_at_beta3_proof,
            val_eval_at_beta3_proof,
            h3_eval_at_beta3_proof,
            g3_eval_at_beta3_proof,
            h2_eval_at_beta2_proof,
            g2_eval_at_beta2_proof,
            h1_eval_at_beta1_proof,
            g1_eval_at_beta1_proof,
            v_eval_at_beta1_proof,
            w_eval_at_beta1_proof,
            h0_eval_at_beta1_proof,
        )

        sum_checks = (sigma3, sigma2)

        poly_commits = (
            h3_poly_commit,
            g3_poly_commit,
            h2_poly_commit,
            g2_poly_commit,
            h1_poly_commit,
            g1_poly_commit,
            v_poly_commit,
            w_poly_commit,
            h0_poly_commit,
        )

        proof = (poly_commits, poly_eval_proofs, sum_checks)

        print(
            f"Successfully created Proof with {len(poly_commits)} PolyCommits, {len(sum_checks)} sumcheck, {len(poly_eval_proofs)} Eval proofs"
        )

        return proof
