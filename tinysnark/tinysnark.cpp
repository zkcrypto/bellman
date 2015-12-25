/*
This is a wrapper around libsnark which provides basic R1CS
zk-SNARK support using the ALT_BN128 curve.
*/

#include "gadgetlib1/gadgets/basic_gadgets.hpp"
#include "zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "common/default_types/r1cs_ppzksnark_pp.hpp"
#include "common/utils.hpp"

using namespace libsnark;
using namespace std;

typedef Fr<default_r1cs_ppzksnark_pp> FieldT;

extern "C" FieldT tinysnark_fieldt_mul(FieldT a, FieldT b) {
    return a * b;
}

extern "C" FieldT tinysnark_fieldt_add(FieldT a, FieldT b) {
    return a + b;
}

extern "C" unsigned long tinysnark_long_from_fieldt(FieldT num) {
    return num.as_bigint().as_ulong();
}

extern "C" FieldT tinysnark_fieldt_from_long(long num) {
    return FieldT(num);
}

extern "C" FieldT tinysnark_fieldt_one() {
    return FieldT::one();
}

extern "C" FieldT tinysnark_fieldt_zero() {
    return FieldT::zero();
}

extern "C" FieldT tinysnark_fieldt_neg(FieldT val) {
    return -val;
}

extern "C" FieldT tinysnark_fieldt_inverse(FieldT val) {
    return val.inverse();
}

extern "C" void tinysnark_init_public_params() {
    default_r1cs_ppzksnark_pp::init_public_params();
    {
        auto p = FieldT::one();
        assert(sizeof(p) == 32);
    }
}

extern "C" void tinysnark_test() {
    protoboard<FieldT> pb;

    linear_combination<FieldT> sum;

    sum = sum + 1;

    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sum, 1), "testing");

    assert(pb.is_satisfied());

    const r1cs_constraint_system<FieldT> constraint_system = pb.get_constraint_system();

    cout << "Number of R1CS constraints: " << constraint_system.num_constraints() << endl;

	auto keypair = r1cs_ppzksnark_generator<default_r1cs_ppzksnark_pp>(constraint_system);

	auto proof = r1cs_ppzksnark_prover<default_r1cs_ppzksnark_pp>(keypair.pk, pb.primary_input(), pb.auxiliary_input());

	r1cs_primary_input<FieldT> input;

	assert(r1cs_ppzksnark_verifier_strong_IC<default_r1cs_ppzksnark_pp>(keypair.vk, input, proof));
}