import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))

from ssbls12 import Fp, Poly, Group
from marlin.fiat_shamir import FiatShamir
from babysnark import G
import copy

def test_fiat_shamir():
	transcript = [Fp(0), 5*G, 123, [4*G, G, 9]]
	fs = FiatShamir()
	ch1 = fs.get_challenge(transcript)
	assert type(ch1) is Fp

	transcript2 = copy.deepcopy(transcript)
	ch2 = fs.get_challenge(transcript2)

	assert ch2 == ch1

	transcript3 = [Fp(1)]
	ch3 = fs.get_challenge(transcript3)

	assert ch3 != ch2 and ch3 != ch1