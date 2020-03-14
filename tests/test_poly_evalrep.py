import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))

from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix, sparsePolynomialsOver
from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver

Fp = FiniteField(
	52435875175126190479447740508185965837690552500527637822603658699938581184513, 1
)  # (# noqa: E501)
Poly = polynomialsOver(Fp)
SparsePoly = sparsePolynomialsOver(Fp)
def test_polyevalrep():
	n = 16
	omega = get_omega(Fp, n)
	PolyEvalRep = polynomialsEvalRep(Fp, omega, n)

	f = Poly([Fp(1), Fp(2), Fp(3), Fp(4), Fp(5)])
	xs = tuple([omega ** i for i in range(n)])
	ys = tuple(map(f, xs))
	# print('xs:', xs)
	# print('ys:', ys)
	f_rep = PolyEvalRep(xs, ys)

	assert f == f_rep.to_coeffs()

	g = f*Poly([Fp(0), Fp(0), Fp(1)])
	g_rep = f_rep._scale(2)
	assert g_rep.to_coeffs() == g


def test_polyeval_divmod():
	n = 16
	omega = get_omega(Fp, n)
	PolyEvalRep = polynomialsEvalRep(Fp, omega, n)

	f = Poly([Fp(1), Fp(2), Fp(3), Fp(4), Fp(5)])

	g = Poly([Fp(6), Fp(7), Fp(8)])

	q1, r1 = divmod(f, g)

	f_rep = PolyEvalRep.from_coeffs(f)
	g_rep = PolyEvalRep.from_coeffs(g)
	print(g, "g here")

	q1_rep, r1_rep = divmod(f_rep, g_rep)

	assert q1_rep.to_coeffs() == q1 and r1_rep.to_coeffs() == r1

def test_sparsepoly():
	f = Poly([Fp(1), Fp(2), Fp(0), Fp(0), Fp(5)])

	g = SparsePoly.from_dense(f)
	assert f == g.to_dense()

	assert f(2092) == g(2092)