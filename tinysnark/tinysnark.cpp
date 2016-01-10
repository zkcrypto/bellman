/*
This is a wrapper around libsnark which provides basic R1CS
zk-SNARK support using the ALT_BN128 curve.
*/

#include "gadgetlib1/gadgets/basic_gadgets.hpp"
#include "zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"
#include "common/default_types/r1cs_ppzksnark_pp.hpp"
#include "common/utils.hpp"
#include "gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp"

using namespace libsnark;
using namespace std;

typedef Fr<default_r1cs_ppzksnark_pp> FieldT;

struct tinysnark_linear_term {
    FieldT coeff;
    size_t index;
};

extern "C" void * tinysnark_gen_proof(void * kp, FieldT* primary, FieldT* aux) {
    r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>* keypair = static_cast<r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>*>(kp);

    r1cs_primary_input<FieldT> primary_input(primary, primary+(keypair->pk.constraint_system.primary_input_size));
    r1cs_auxiliary_input<FieldT> aux_input(aux, aux+(keypair->pk.constraint_system.auxiliary_input_size));

    auto proof = new r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp>(
        r1cs_ppzksnark_prover<default_r1cs_ppzksnark_pp>(keypair->pk, primary_input, aux_input)
    );

    return static_cast<void*>(std::move(proof));
}

extern "C" bool tinysnark_verify_proof(void * iproof, void * kp, FieldT* primary) {
    r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp>* proof = static_cast<r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp>*>(iproof);
    r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>* keypair = static_cast<r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>*>(kp);

    r1cs_primary_input<FieldT> primary_input(primary, primary+(keypair->pk.constraint_system.primary_input_size));

    return r1cs_ppzksnark_verifier_strong_IC<default_r1cs_ppzksnark_pp>(keypair->vk, primary_input, *proof);
}

extern "C" void * tinysnark_drop_proof(void * proof) {
    r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp>* p = static_cast<r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp>*>(proof);

    delete p;
}

extern "C" void * tinysnark_gen_keypair(void * ics) {
    r1cs_constraint_system<FieldT>* cs = static_cast<r1cs_constraint_system<FieldT>*>(ics);

    auto keypair = new r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>(
        r1cs_ppzksnark_generator<default_r1cs_ppzksnark_pp>(*cs)
    );

    return static_cast<void*>(std::move(keypair));
}

extern "C" void * tinysnark_drop_keypair(void * kp) {
    r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>* k = static_cast<r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp>*>(kp);

    delete k;
}

extern "C" void * tinysnark_new_r1cs(size_t primary_size, size_t aux_size) {
    auto cs = new r1cs_constraint_system<FieldT>();

    cs->primary_input_size = primary_size;
    cs->auxiliary_input_size = aux_size;

    return static_cast<void*>(std::move(cs));
}

extern "C" void tinysnark_drop_r1cs(void * ics) {
    r1cs_constraint_system<FieldT>* cs = static_cast<r1cs_constraint_system<FieldT>*>(ics);

    delete cs;
}

extern "C" bool tinysnark_satisfy_test(void * ics, FieldT* primary, FieldT* aux) {
    r1cs_constraint_system<FieldT>* cs = static_cast<r1cs_constraint_system<FieldT>*>(ics);

    r1cs_primary_input<FieldT> primary_input(primary, primary+(cs->primary_input_size));
    r1cs_auxiliary_input<FieldT> aux_input(aux, aux+(cs->auxiliary_input_size));

    return cs->is_valid() && cs->is_satisfied(primary_input, aux_input);
}

extern "C" void * tinysnark_add_constraint(
    void * ics,
    tinysnark_linear_term * a_terms,
    size_t a_terms_len,
    tinysnark_linear_term * b_terms,
    size_t b_terms_len,
    tinysnark_linear_term * c_terms,
    size_t c_terms_len
) {
    r1cs_constraint_system<FieldT>* cs = static_cast<r1cs_constraint_system<FieldT>*>(ics);

    std::vector<linear_term<FieldT>> a;
    std::vector<linear_term<FieldT>> b;
    std::vector<linear_term<FieldT>> c;

    for (size_t i = 0; i < a_terms_len; i++) {
        FieldT coeff = a_terms[i].coeff;
        size_t index = a_terms[i].index;

        a.push_back(linear_term<FieldT>(variable<FieldT>(index), coeff));
    }

    for (size_t i = 0; i < b_terms_len; i++) {
        FieldT coeff = b_terms[i].coeff;
        size_t index = b_terms[i].index;

        b.push_back(linear_term<FieldT>(variable<FieldT>(index), coeff));
    }

    for (size_t i = 0; i < c_terms_len; i++) {
        FieldT coeff = c_terms[i].coeff;
        size_t index = c_terms[i].index;

        c.push_back(linear_term<FieldT>(variable<FieldT>(index), coeff));
    }

    linear_combination<FieldT> a_lc(a);
    linear_combination<FieldT> b_lc(b);
    linear_combination<FieldT> c_lc(c);

    r1cs_constraint<FieldT> constraint(a_lc, b_lc, c_lc);

    cs->add_constraint(constraint);
}

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
    typedef Fr<default_r1cs_ppzksnark_pp> FieldT;

    protoboard<FieldT> pb;

    auto input_bits = new digest_variable<FieldT>(pb, 512, "input_bits");
    auto output_bits = new digest_variable<FieldT>(pb, 256, "output_bits");
    auto input_block = new block_variable<FieldT>(pb, {
        input_bits->bits
    }, "input_block");
    auto IV = SHA256_default_IV(pb);
    auto sha256 = new sha256_compression_function_gadget<FieldT>(pb,
                                                          IV,
                                                          input_block->bits,
                                                          *output_bits,
                                                          "sha256");

    input_bits->generate_r1cs_constraints();
    output_bits->generate_r1cs_constraints();
    sha256->generate_r1cs_constraints();

    const r1cs_constraint_system<FieldT> constraint_system = pb.get_constraint_system();

    cout << "Number of R1CS constraints: " << constraint_system.num_constraints() << endl;
}