"""
Simple end to end test for Marlin
"""
import sys, os

sys.path.append(os.path.realpath(os.path.dirname(__file__) + "/.."))
from universal_setup import UniversalSetup
from circuit import BooleanCircuit
from indexer import Indexer
from prover import Prover
from verifier import Verifier
from util import isPowerOfTwo
def test_marlin():
	# Create the universal setup
	max_num_constraints = 10
	max_non_zero_elems = 15
	max_num_variables = 10
	srs = UniversalSetup(max_num_constraints, max_num_variables, max_non_zero_elems).CRS

	##Offline Phase: Create an Index for a corresponding Circuit
	# Index a particular circuit
	circuit_filename = "circuits/xor.txt"
	circuit = BooleanCircuit(file_name = circuit_filename)
	circuit_index = Indexer(circuit, srs)
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
	assert isPowerOfTwo(n_stmt), \
	"Current implementation only supports statemnts of power of Two"
	# Split a according to x(stmt) and w(witness). 
	x = a[:n_stmt]
	w = a[n_stmt:]

	# Initialize the prover with statment and witness assignments
	# with the indexer pk and vk.
	prover = Prover(x, w, index_pk, index_vk)
	# Initilize the Verifier with the verification key and statement
	verifier = Verifier(x, index_vk)
	"""
	Get the prover oracles for the first round, the orcales in this 
	case are (v_poly and w_poly) representing U*a and a repectively
	"""
	first_round_oracles = prover.first_round_prover()

	# Get the verifier challenges alpha and eta
	alpha, eta = verifier.verifier_first_message() 



test_marlin()
