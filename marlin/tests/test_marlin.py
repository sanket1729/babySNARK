"""
Simple end to end test for Marlin
"""
import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/../.."))
sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))
from universal_setup import UniversalSetup
from circuit import BooleanCircuit
from indexer import Indexer
from prover import Prover
from verifier import Verifier
from util import isPowerOfTwo
from babysnark import evaluate_in_exponent
from polycommit import PolyCommit


def test_marlin():
    # Create the universal setup
    max_num_constraints = 10
    max_non_zero_elems = 15
    max_num_variables = 10
    srs = UniversalSetup(max_num_constraints, max_num_variables, max_non_zero_elems).CRS
    pc = PolyCommit(crs=srs)

    ##Offline Phase: Create an Index for a corresponding Circuit
    # Index a particular circuit
    circuit_filename = "circuits/xor.txt"
    circuit = BooleanCircuit(file_name=circuit_filename)
    circuit_index = Indexer(circuit, pc)
    # Call the indexer, get the indexer public key and verification key
    index_pk, index_vk = circuit_index.index()

    # Online Phase:
    """
	Note the difference between inputs, outputs, statements and witness
	Inputs: Inputs to circuit. Wires to the circuit which don't have 
			any preceding inputs. Ex: Input Block of 512 bits to SHA2 circuit
	Outputs: Last layer of the circuit. Wires which don't any more 
			outgoing connection
	Statement: Claimed evaluations about a subset of wires by the prover.
			Usually, we set the output of the wires as the statement.
	Witness: All other wires values which are statements are by default witness
	"""

    # Get some random input for the circuit
    inputs = circuit.get_random_inputs()
    # Generate witness and statements from the random
    # input for the prover
    n_stmt, a = circuit.solve_ssp_instance(inputs, circuit_index.U)
    assert isPowerOfTwo(
        n_stmt
    ), "Current implementation only supports statemnts of power of Two"
    # Split a according to x(stmt) and w(witness).
    x = a[:n_stmt]
    w = a[n_stmt:]

    # Initilize the Verifier with the verification key and statement
    verifier = Verifier(index_vk)
    # Initialize the prover with
    # with the indexer pk and vk
    prover = Prover(index_pk, index_vk)

    # Obtain proof for (x, w)
    # Verfier is also passed along for getting challenges
    proof = prover.prove(x, w)

    # Finally assert the proof with the stored challenges
    # in verifier
    assert verifier.verify(x, proof)
