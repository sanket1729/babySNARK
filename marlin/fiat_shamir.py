import hashlib

"""
Simple class for fiat shamir
Can be extended to multple challenges in future

For now, this assumes group elements in Fp, and groups
according to ssbls12. 
Generalizing this remains a future work
"""
from ssbls12 import Fp, Group
class FiatShamir:
	"""
	Returns a challenge in Fp
	"""
	def get_challenge(self, transcript):
		m = hashlib.sha256()
		for elem in transcript:
			if type(elem) in [Fp, Group, int]:
				m.update(repr(elem).encode())
			elif type(elem) is list:
				for item in elem:
					assert type(item) in [Fp, Group, int]
					m.update(repr(item).encode())
			else:
				raise Exception(f"{type(elem)} Currently FiatShamir transcript"+ 
					"is only Fp, int and EC Group elems")

		digest = m.digest()

		ch = int.from_bytes(digest, 'big')
		while ch >= Fp.p:
			# Go again, if the hash range is outside challenge space
			m.update(b"Another try!")
			digest = m.digest()
			ch = int.from_bytes(digest, 'big')

		return Fp(ch)