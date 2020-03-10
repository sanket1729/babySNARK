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
from babysnark import evaluate_in_exponent
from polycommit import PolyCommit


def test_marlin():
	# Create the universal setup
	max_num_constraints = 10
	max_non_zero_elems = 15
	max_num_variables = 10
	srs = UniversalSetup(max_num_constraints, max_num_variables, max_non_zero_elems).CRS
	pc = PolyCommit(crs = srs)

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

	# Commit to the prover first round oracles
	(w_poly, v_poly, h0_poly) = first_round_oracles
	w_poly_commit = pc.commit(w_poly)
	v_poly_commit = pc.commit(v_poly)
	h0_poly_commit = pc.commit(h0_poly)

	# Get the verifier challenges alpha and eta
	alpha = verifier.verifier_first_message()

	second_round_oracles = prover.prover_second_round(alpha)

	(h1_poly, g1_poly) = second_round_oracles

	h1_poly_commit = pc.commit(h1_poly)
	g1_poly_commit = pc.commit(g1_poly)

	beta1 = verifier.verifier_second_message()

	third_round_oracles, sigma2 = prover.prover_third_round(alpha, beta1)

	h2_poly, g2_poly = third_round_oracles

	h2_poly_commit = pc.commit(h2_poly)
	g2_poly_commit = pc.commit(g2_poly)

	beta2 = verifier.verifier_third_message()

	fourth_round_oracles, sigma3 = prover.prover_fourth_round(alpha, beta1, beta2)

	h3_poly, g3_poly = third_round_oracles

	h3_poly_commit = pc.commit(h3_poly)
	g3_poly_commit = pc.commit(g3_poly)

	beta3 = verifier.verifier_fourth_message()

	"""
	h3(X)*vanish_k(X) = a(X) - b(X)*(X*G(X) + sigma3/|K|) at beta3
	In the equation, needs to give oracle proofs for row, col, val, 
	h and g at beta3
	"""
	h3_eval_at_beta3_proof = pc.create_witness(h3_poly, beta3)
	g3_eval_at_beta3_proof = pc.create_witness(g3_poly, beta3)
	row_eval_at_beta3_proof = pc.create_witness(circuit_index.row_poly, beta3)
	col_eval_at_beta3_proof = pc.create_witness(circuit_index.col_poly, beta3)
	val_eval_at_beta3_proof = pc.create_witness(circuit_index.val_poly, beta3)

	"""
	r(alpa, X)*sigma3 = h2(X)*vanish_h(X) + X*g2(X) + sigma2/|H| at beta2
	Again, the verifier can get other terms all by himself, he only
	needs oracle access to h2 and g2 with eval proofs
	"""
	h2_eval_at_beta2_proof = pc.create_witness(h2_poly, beta2)
	g2_eval_at_beta2_proof = pc.create_witness(g2_poly, beta2)

	"""
	r(alpa, X)*V(X) - sigma2*w(X) = h1(X)*vanish_h(X) + X*g2(X) at beta1
	Again, the verifier can get other terms all by himself, he only
	needs oracle access to v, w, h1 and g1 with eval proofs
	The verifier will extend w with this public input
	to make sure that statements is indeed satisfied.
	"""
	h1_eval_at_beta1_proof = pc.create_witness(h1_poly, beta1)
	g1_eval_at_beta1_proof = pc.create_witness(g1_poly, beta1)
	v_eval_at_beta1_proof = pc.create_witness(v_poly, beta1)
	w_eval_at_beta1_proof = pc.create_witness(w_poly, beta1)

	"""
	The final rowcheck which is similar to babysnark, checking
	whether v(X)*v(X) = h0(X)*vanish_h(X) at beta1.
	We only need value of h0(X) at beta1
	"""
	h0_eval_at_beta1_proof = pc.create_witness(h0_poly, beta1)

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

	return proof

test_marlin()
