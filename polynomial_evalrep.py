# | # Evaluation Representation of Polynomials and FFT optimizations
# | In addition to the coefficient-based representation of polynomials used
# | in babysnark.py, for performance we will also use an alternative
# | representation where the polynomial is evaluated at a fixed set of points.
# | Some operations, like multiplication and division, are significantly more
# | efficient in this form.
# | We can use FFT-based tools for efficiently converting
# | between coefficient and evaluation representation.
# |
# | This library provides:
# |  - Fast fourier transform for finite fields
# |  - Interpolation and evaluation using FFT

from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from finitefield.euclidean import extendedEuclideanAlgorithm
import random
from finitefield.numbertype import typecheck, memoize, DomainElement
from functools import reduce
import numpy as np
from util import isPowerOfTwo, nearestPowerOfTwo


# | ## Choosing roots of unity
def get_omega(field, n, seed=None):
	"""
	Given a field, this method returns an n^th root of unity.
	If the seed is not None then this method will return the
	same n'th root of unity for every run with the same seed

	This only makes sense if n is a power of 2.
	"""
	rnd = random.Random(seed)
	assert n & n - 1 == 0, "n must be a power of 2"
	x = field(rnd.randint(0, field.p - 1))
	y = pow(x, (field.p - 1) // n)
	if y == 1 or pow(y, n // 2) == 1:
		return get_omega(field, n)
	assert pow(y, n) == 1, "omega must be 2n'th root of unity"
	assert pow(y, n // 2) != 1, "omega must be primitive 2n'th root of unity"
	return y


# | ## Fast Fourier Transform on Finite Fields
def fft_helper(a, omega, field):
	"""
	Given coefficients A of polynomial this method does FFT and returns
	the evaluation of the polynomial at [omega^0, omega^(n-1)]

	If the polynomial is a0*x^0 + a1*x^1 + ... + an*x^n then the coefficients
	list is of the form [a0, a1, ... , an].
	"""
	n = len(a)
	assert not (n & (n - 1)), "n must be a power of 2"

	if n == 1:
		return a

	b, c = a[0::2], a[1::2]
	b_bar = fft_helper(b, pow(omega, 2), field)
	c_bar = fft_helper(c, pow(omega, 2), field)
	a_bar = [field(1)] * (n)
	for j in range(n):
		k = j % (n // 2)
		a_bar[j] = b_bar[k] + pow(omega, j) * c_bar[k]
	return a_bar


# | ## Representing a polynomial by evaluation at fixed points
@memoize
def polynomialsEvalRep(field, omega, n):
	assert n & n - 1 == 0, "n must be a power of 2"

	# Check that omega is an n'th primitive root of unity
	assert type(omega) is field
	omega = field(omega)
	assert omega ** (n) == 1
	_powers = [omega ** i for i in range(n)]
	assert len(set(_powers)) == n

	_poly_coeff = polynomialsOver(field)

	class PolynomialEvalRep(object):
		def __init__(self, xs, ys):
			# Each element of xs must be a power of omega.
			# There must be a corresponding y for every x.
			if type(xs) is not tuple:
				xs = tuple(xs)
			if type(ys) is not tuple:
				ys = tuple(ys)

			assert len(xs) <= n + 1
			assert len(xs) == len(ys)
			for x in xs:
				assert x in _powers
			for y in ys:
				assert type(y) is field, type(y)

			self.evalmap = dict(zip(xs, ys))

		@classmethod
		def from_coeffs(cls, poly):
			assert type(poly) is _poly_coeff
			assert poly.degree() <= n
			padded_coeffs = poly.coefficients + [field(0)] * (
				n - len(poly.coefficients)
			)
			ys = fft_helper(padded_coeffs, omega, field)
			xs = [omega ** i for i in range(n) if ys[i] != 0]
			ys = [y for y in ys if y != 0]
			return cls(xs, ys)

		def to_coeffs(self):
			# To convert back to the coefficient form, we use polynomial interpolation.
			# The non-zero elements stored in self.evalmap, so we fill in the zero values
			# here.
			ys = [self.evalmap[x] if x in self.evalmap else field(0) for x in _powers]
			coeffs = [b / field(n) for b in fft_helper(ys, 1 / omega, field)]
			return _poly_coeff(coeffs)


		def __call__(self, x):
			if type(x) is int:
				x = field(x)
			assert type(x) is field
			xs = _powers

			# Efficient algorithm to get all lagrange polyevals when 
			# all x's form a multiplicative subgroup
			def get_all_lagrange_values(x):
				
				# Stores the evals of all lagrange_polys
				lagrange_evals = []
				x_pow_n = x**n
				# First case is when x is itself in powers
				if x_pow_n is field(1):
					# Only 1 eval will be 1 rest, all will be zero
					lagrange_evals = [field(0)]*n
					lagrange_evals[_powers.index(x)] = field(1)
					return lagrange_evals
				else:
					# x is not in poowers.
					# Initial value of l is basically the product of all
					# terms (x - xi) 
					l = (x_pow_n - field(1))/field(n)
					r = field(1)
					ls = []

					# Compute all the products and then multiply by
					# inverse
					for i in range(n):
						lagrange_evals.append(field(1)/(x - r))
						ls.append(l)
						l *= omega
						r *= omega

					for i in range(n):
						lagrange_evals[i] *= ls[i]

					return lagrange_evals

			y = field(0)
			lagrange_evals = get_all_lagrange_values(x)
			for i, xi in enumerate(_powers):
				if xi in self.evalmap:
					yi = self.evalmap[xi]
					y += yi * lagrange_evals[i]
			return y

		def __mul__(self, other):
			# Scale by integer
			if type(other) is int:
				other = field(other)
			if type(other) is field:
				return PolynomialEvalRep(
					self.evalmap.keys(), [other * y for y in self.evalmap.values()]
				)

			# Multiply another polynomial in the same representation
			if type(other) is type(self):
				xs = []
				ys = []
				for x, y in self.evalmap.items():
					if x in other.evalmap:
						xs.append(x)
						ys.append(y * other.evalmap[x])
				return PolynomialEvalRep(xs, ys)

		def _scale(self, d):
			# Scale the current polynomial by multiplying by x^d
			poly = self.to_coeffs()
			assert d + poly.degree() < n
			if d >=0:
				new_poly = _poly_coeff([field(0)]*d + poly.coefficients)
				return PolynomialEvalRep.from_coeffs(new_poly)
			else:
				new_poly = _poly_coeff(poly.coefficients[-d:])
				return PolynomialEvalRep.from_coeffs(new_poly)

		def _reciprocal(self):
			# Create a inverse of the current polynomial 
			# Calculate the reciprocal of polynomial ``p(x)`` with degree ``k-1``,
			# defined as: ``x^(2k-2) / p(x)``, where ``k`` is a power of 2.
			poly = self.to_coeffs()
			k = poly.degree() + 1
			assert isPowerOfTwo(k) and poly.coefficients[-1] != field(0)

			assert 2*k < n, "Multiplication Domain not sufficient for EvalRep"

			if k == 1:
				return PolynomialEvalRep.from_coeffs(_poly_coeff([field(1/ poly.coefficients[0])]))
			else:
				q = PolynomialEvalRep.from_coeffs(_poly_coeff(poly.coefficients[k//2:]))._reciprocal()
				r = (q*2)._scale(3*k//2 - 2) - ((q*q)*self)

				return r._scale(-k + 2)

		# Takes in two polynomials in eval_rep form and returns a 
		# qoutient and remainder
		# NOTE: The Eval Rep degree representation must be atleast twice 
		# as the maximum polynomial degree
		def __divmod__(self, other):
			# Based on notes: http://web.cs.iastate.edu/~cs577/handouts/polydivide.pdf
			# And https://stackoverflow.com/questions/44770632/fft-division-for-fast-polynomial-division
			poly = self.to_coeffs()
			other_poly = other.to_coeffs()

			# Ensure that degree other is one less power of two
			pow2 = nearestPowerOfTwo(other_poly.degree()+1)
			extra_degree_reqd = pow2 - other_poly.degree() - 1
			if extra_degree_reqd != 0:
				other_polyrep = other._scale(extra_degree_reqd)
				polyrep = self._scale(extra_degree_reqd)

			deg = polyrep.to_coeffs().degree()
			other_deg = other_polyrep.to_coeffs().degree()

			inv = other_polyrep._reciprocal()
			q = polyrep*inv
			q = q._scale( -2 * other_deg)

			# handle the case when deg> 2 * other_deg 
			if deg > 2 * other_deg:
				# t = x^2other_deg - inv*other
				x_pow_2n = PolynomialEvalRep.from_coeffs(_poly_coeff( [field(0)]*other_deg + [field(1)]))
				t2 = inv*other_polyrep
				t = x_pow_2n - t2

				new_polyrep = (polyrep*t)._scale(-2 * other_deg)
				q2, r2 = new_polyrep.__divmod__(other_polyrep)
				q += q2

			r = self - other*q
			return q, r


		@typecheck
		def __iadd__(self, other):
			# Add another polynomial to this one in place.
			# This is especially efficient when the other polynomial is sparse,
			# since we only need to add the non-zero elements.
			for x, y in other.evalmap.items():
				if x not in self.evalmap:
					self.evalmap[x] = y
				else:
					self.evalmap[x] += y
			return self

		@typecheck
		def __add__(self, other):
			res = PolynomialEvalRep(self.evalmap.keys(), self.evalmap.values())
			res += other
			return res

		def __sub__(self, other):
			return self + (-other)

		def __neg__(self):
			return PolynomialEvalRep(
				self.evalmap.keys(), [-y for y in self.evalmap.values()]
			)

		def __truediv__(self, divisor):
			# Scale by integer
			if type(divisor) is int:
				other = field(divisor)
			if type(divisor) is field:
				return self * (1 / divisor)
			if type(divisor) is type(self):
				res = PolynomialEvalRep((), ())
				for x, y in self.evalmap.items():
					assert x in divisor.evalmap
					res.evalmap[x] = y / divisor.evalmap[x]
				return res
			return NotImplemented

		def __copy__(self):
			return PolynomialEvalRep(self.evalmap.keys(), self.evalmap.values())

		def __repr__(self):
			return (
				f"PolyEvalRep[{hex(omega.n)[:15]}...,{n}]({len(self.evalmap)} elements)"
			)

		@classmethod
		def divideWithCoset(cls, p, t, c=field(3)):
			"""
			  This assumes that p and t are polynomials in coefficient representation,
			and that p is divisible by t.
			   This function is useful when t has roots at some or all of the powers of omega,
			in which case we cannot just convert to evalrep and use division above
			(since it would cause a divide by zero.
			   Instead, we evaluate p(X) at powers of (c*omega) for some constant cofactor c.
			To do this efficiently, we create new polynomials, pc(X) = p(cX), tc(X) = t(cX),
			and evaluate these at powers of omega. This conversion can be done efficiently
			on the coefficient representation.
			   See also: cosetFFT in libsnark / libfqfft.
			   https://github.com/scipr-lab/libfqfft/blob/master/libfqfft/evaluation_domain/domains/extended_radix2_domain.tcc
			"""
			assert type(p) is _poly_coeff
			assert type(t) is _poly_coeff
			# Compute p(cX), t(cX) by multiplying coefficients
			c_acc = field(1)
			pc = _poly_coeff(list(p.coefficients))  # make a copy
			for i in range(p.degree() + 1):
				pc.coefficients[-i - 1] *= c_acc
				c_acc *= c
			c_acc = field(1)
			tc = _poly_coeff(list(t.coefficients))  # make a copy
			for i in range(t.degree() + 1):
				tc.coefficients[-i - 1] *= c_acc
				c_acc *= c

			# Divide using evalrep
			pc_rep = cls.from_coeffs(pc)
			tc_rep = cls.from_coeffs(tc)
			hc_rep = pc_rep / tc_rep
			hc = hc_rep.to_coeffs()

			# Compute h(X) from h(cX) by dividing coefficients
			c_acc = field(1)
			h = _poly_coeff(list(hc.coefficients))  # make a copy
			for i in range(hc.degree() + 1):
				h.coefficients[-i - 1] /= c_acc
				c_acc *= c

			# Correctness checks
			# assert pc == tc * hc
			# assert p == t * h
			return h

	return PolynomialEvalRep


@memoize
def sparsePolynomialsOver(field):
	# | ## Sparse Polynomial
	# | In our setting, sometimes we expect to evaluate a polynomial which only
	# | has sparse entires in coefficients. 
	# | In this setting, it's appropriate to use a dict representation - 
	# | which is a mapping between coeffient index and the corresponding 
	# | value of that coefficient.

	_poly_coeff = polynomialsOver(field) 
	class SparsePoly(object):
		# Only a few necessary methods are included here.

		def __init__(self, c = None):
			if type(c) is SparsePoly:
				self.coeff_map = c.coeff_map
			elif isinstance(c, dict):
				self.coeff_map = c
			elif c is None:
				self.coeff_map = dict()
			else:
				raise Execption("Sparse Must be initialized with a dict")
			self.zero = field(0)

		def isZero(self):
			return len(self.coeff_map) == 0

		def __repr__(self):
			return repr(self.coeff_map)

		def __call__(self, x):
			if type(x) is int:
				x = field(x)

			ret = field(0)
			for k, v in self.items():
				ret += (x**k) *v
			return ret

		def __setitem__(self, key, v):
			assert type(key) is int
			if type(v) is int:
				v = field(v)
			self.coeff_map[key] = v

		def __getitem__(self, key):
			return self.coeff_map[key] if key in self.coeff_map else self.zero

		def items(self):
			for i in self.coeff_map:
					yield i, self.coeff_map[i]

		def to_dense(self):
			max_deg = max(self.coeff_map.keys())
			coefficients = [0]*(max_deg + 1)
			for key, val in self.items():
				coefficients[key] = val
			return _poly_coeff(coefficients)

		@classmethod
		def from_dense(cls, dense):
			coeff_map = dict()	
			for i, coeff in enumerate(dense.coefficients):
				if coeff != field(0):
					coeff_map[i] = coeff
			return cls(coeff_map)

	return SparsePoly

# | ## Sparse Matrix
# | In our setting, we have O(m*m) elements in the matrix, and expect the number of
# | elements to be O(m).
# | In this setting, it's appropriate to use a rowdict representation - a dense
# | array of dictionaries, one for each row, where the keys of each dictionary
# | are column indices.


class RowDictSparseMatrix:
	# Only a few necessary methods are included here.
	# This could be replaced with a generic sparse matrix class, such as scipy.sparse,
	# but this does not work as well with custom value types like Fp

	def __init__(self, m, n, zero=None):
		self.m = m
		self.n = n
		self.shape = (m, n)
		self.zero = zero
		self._len = 0
		self.rowdicts = [dict() for _ in range(m)]

	def __setitem__(self, key, v):
		i, j = key
		if j not in self.rowdicts[i]:
			self._len += 1
		self.rowdicts[i][j] = v

	def __getitem__(self, key):
		i, j = key
		return self.rowdicts[i][j] if j in self.rowdicts[i] else self.zero

	def items(self):
		for i in range(self.m):
			for j, v in self.rowdicts[i].items():
				yield (i, j), v

	def rows(self):
		for i in range(self.m):
			yield self.rowdicts[i]

	def dot(self, other):
		if isinstance(other, np.ndarray):
			assert other.dtype == "O"
			assert other.shape in ((self.n,), (self.n, 1))
			ret = np.empty((self.m,), dtype="O")
			ret.fill(self.zero)
			for i in range(self.m):
				for j, v in self.rowdicts[i].items():
					ret[i] += other[j] * v
			return ret

	def to_dense(self):
		mat = np.empty((self.m, self.n), dtype="O")
		mat.fill(self.zero)
		for (i, j), val in self.items():
			mat[i, j] = val
		return mat

	def __repr__(self):
		return repr(self.rowdicts)

	def num_non_zero_elems(self):
		return self._len


# Examples
if __name__ == "__main__":
	Fp = FiniteField(
		52435875175126190479447740508185965837690552500527637822603658699938581184513, 1
	)  # (# noqa: E501)
	Poly = polynomialsOver(Fp)

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
