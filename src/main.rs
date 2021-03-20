use array_init::array_init;
use oracle::{poseidon_5_wires::*, poseidon::{SpongeConstants, Sponge, ArithmeticSpongeParams}, sponge_5_wires::{DefaultFqSponge, DefaultFrSponge}};
use plonk_5_wires_circuits::{wires::Wire, gate::{GateType, CircuitGate}, constraints::ConstraintSystem};
use commitment_dlog::{srs::{SRS, SRSSpec, endos}, commitment::{PolyComm, CommitmentCurve, ceil_log2, b_poly_coefficients}};
use algebra::{AffineCurve, ProjectiveCurve, PrimeField, FftField, SquareRootField, Field, BigInteger, SWModelParameters,
    pasta::{pallas::{Affine as Other, PallasParameters}, vesta::{Affine, VestaParameters},
    fq::Fq,
    fp::Fp}, One, Zero, UniformRand};
use plonk_5_wires_protocol_dlog::{prover::{ProverProof}, index::{Index, VerifierIndex}};
use groupmap::GroupMap;

mod fft;
mod endo;
mod random_oracle;
mod schnorr;
mod bba;
mod bba_update_proof;
mod bba_init_proof;
mod bba_open_proof;
mod proof_system;
mod util;
use proof_system::*;
use util::*;

use schnorr::*;

type SpongeQ = DefaultFqSponge<VestaParameters, PlonkSpongeConstants>;
type SpongeR = DefaultFrSponge<Fp, PlonkSpongeConstants>;

fn main() {
    let (_endo_q, endo_r) = endos::<Other>();
    let signer = Signer::<Other> {
        sponge: oracle::pasta::fp5::params(),
        endo: endo_r
    };
    {
        let m = Other::prime_subgroup_generator();
        let k = <Other as AffineCurve>::ScalarField::rand(&mut rand_core::OsRng);
        let pubkey = Other::prime_subgroup_generator().mul(k).into_affine();
        let s = signer.sign(k, m);
        assert!(signer.verify(pubkey, m, s));
    }

    let other_srs = SRS::<Other>::create(1 << 11);
    let srs = SRS::<Affine>::create(1 << 11);
    let group_map = <Affine as CommitmentCurve>::Map::setup();

    let proof_system_constants = fp_constants();

    {
        let brave_sk = <Other as AffineCurve>::ScalarField::rand(&mut rand_core::OsRng);
        let brave_pubkey = Other::prime_subgroup_generator().mul(brave_sk).into_affine();

        let bba = time("BBA parameter precomputation", || bba::Params::new(&other_srs, endo_r));

        let h = other_srs.h.to_coordinates().unwrap();
        let init_params = bba_init_proof::Params {
            l0: bba.lagrange_commitments[0].to_coordinates().unwrap(), 
            h,
        };

        let update_params = bba_update_proof::Params {
            brave_pubkey: brave_pubkey.to_coordinates().unwrap(),
            h,
        };

        let init_pk = generate_proving_key(&srs, 2, |sys, p| {
            bba_init_proof::circuit::<_, Other, _>(&init_params, &None, sys, p)
        });
        let init_vk = init_pk.verifier_index();

        let update_pk = generate_proving_key(&srs, 2, |sys, p| {
            bba_update_proof::circuit::<_, Other, _>(&proof_system_constants, &update_params, &None, sys, p)
        });
        let update_vk = update_pk.verifier_index();

        let other_lgr_comms : Vec<PolyComm<Affine>> = time("lagrange commitment precomputation", ||
            fft::lagrange_commitments(&srs).iter()
            .map(|g| PolyComm { unshifted: vec![*g], shifted: None }).collect());

        // The value representing the state of the update authority (e.g., Brave)
        let update_authority = bba::UpdateAuthority {
            signing_key: brave_sk,
            signer: signer.clone(),
            group_map: group_map.clone(),
            init_vk,
            other_lgr_comms,
            lgr_comms: bba.lagrange_commitments.clone(),
            update_vk,
        };

        let user_config = bba::UserConfig {
            signer: signer.clone(),
            bba: bba.clone(),
            authority_public_key: brave_pubkey,
            prover: bba::UserProver {
                group_map: group_map.clone(),
                proof_system_constants: proof_system_constants.clone(),
                init_params: init_params.clone(),
                update_params: update_params.clone(),
                init_pk,
                update_pk,
            }
        };

        // First, the user requests an initial BBA from the authority
        let init_secrets = bba::init_secrets();
        let init_request = user_config.request_init::<SpongeQ, SpongeR>(init_secrets);
        let init_signature = update_authority.perform_init::<SpongeQ, SpongeR>(init_request).unwrap();
    }

    /*
    {
        let brave_sk = <Other as AffineCurve>::ScalarField::rand(&mut rand_core::OsRng);
        let brave_pubkey = Other::prime_subgroup_generator().mul(brave_sk).into_affine().to_coordinates().unwrap();

        let bba = time("BBA parameter precomputation", || bba::Params::new(&other_srs, endo_r));

        let params = bba_update_proof::Params {
            brave_pubkey, 
            h: other_srs.h.to_coordinates().unwrap()
        };

        let index = generate_proving_key(&srs, 2, |sys, p| {
            bba_update_proof::circuit::<_, Other, _>(&constants, &params, &None, sys, p)
        });
        let verifier_index = index.verifier_index();

        // Dummy accumulator
        let acc = Other::prime_subgroup_generator().mul(Fq::rand(&mut rand_core::OsRng)).into_affine();
        let signature = signer.sign(brave_sk, acc);

        let bba::Randomized { result: new_acc, witness:endo::EndoScalar(r) } = bba.randomize(acc);

        let witness = bba_update_proof::Witness {
            acc,
            signature,
            r
        };

        let new_acc = new_acc.to_coordinates().unwrap();

        // a + 2^{n - 1}
        let proof = time("proving time", ||
            prove(&index, &group_map, vec![new_acc.0, new_acc.1], |sys, p| {
                bba_update_proof::circuit(&constants, &params, &Some(witness), sys, p)
            }));

        let lgr_comms : Vec<PolyComm<Affine>> =
            fft::lagrange_commitments(&srs).iter()
            .map(|g| PolyComm { unshifted: vec![*g], shifted: None }).collect();

        let num_proofs = 100;

        let _ = time("verify 100 proofs", || {
            let proofs = vec![(&verifier_index, &lgr_comms, &proof); num_proofs];
            assert!(
                ProverProof::verify::<DefaultFqSponge<VestaParameters, PlonkSpongeConstants>, DefaultFrSponge<Fp, PlonkSpongeConstants>>
                (&group_map, &proofs).unwrap());
        });
    } */
}
