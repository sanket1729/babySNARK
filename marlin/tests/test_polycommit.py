from ssbls12 import Fp, Poly, Group
from polycommit import PolyCommit


def test_polycommit():
    f = Poly([Fp(1), Fp(4), Fp(2), Fp(3)])
    pc = PolyCommit(max_degree=5)
    C = pc.commit(f)
    i = Fp(10)
    proof = pc.create_witness(f, i)

    assert pc.verify_eval(C, proof)
