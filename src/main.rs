use algebra::{
    pasta::{
        fp::Fp,
        fq::Fq,
        pallas::{Affine as Other, PallasParameters},
        vesta::{Affine, VestaParameters},
    },
    AffineCurve, ProjectiveCurve,
    UniformRand,
};
use commitment_dlog::{
    commitment::{ceil_log2, CommitmentCurve, PolyComm},
    srs::{endos, SRS},
};
use groupmap::GroupMap;
use oracle::{
    poseidon_5_wires::*,
    sponge_5_wires::{DefaultFqSponge, DefaultFrSponge},
};

mod bba;
mod bba_init_proof;
mod bba_open_proof;
mod bba_update_proof;
mod endo;
mod fft;
mod proof_system;
mod random_oracle;
mod schnorr;
mod util;
use proof_system::*;
use util::*;

use schnorr::*;

type SpongeQ = DefaultFqSponge<VestaParameters, PlonkSpongeConstants>;
type SpongeR = DefaultFrSponge<Fp, PlonkSpongeConstants>;

type PSpongeQ = DefaultFqSponge<PallasParameters, PlonkSpongeConstants>;
type PSpongeR = DefaultFrSponge<Fq, PlonkSpongeConstants>;

fn main() {
    let (_endo_q, endo_r) = endos::<Other>();
    let signer = Signer::<Other> {
        sponge: oracle::pasta::fp5::params(),
        endo: endo_r,
    };
    {
        let m = Other::prime_subgroup_generator();
        let k = <Other as AffineCurve>::ScalarField::rand(&mut rand_core::OsRng);
        let pubkey = Other::prime_subgroup_generator().mul(k).into_affine();
        let s = signer.sign(k, m);
        assert!(signer.verify(pubkey, m, s));
    }

    let other_srs = SRS::<Other>::create(1 << ceil_log2(bba::MAX_COUNTERS));
    let srs = SRS::<Affine>::create(1 << 11);
    let group_map = <Affine as CommitmentCurve>::Map::setup();
    let g_group_map = <Other as CommitmentCurve>::Map::setup();

    let proof_system_constants = fp_constants();
    let fq_proof_system_constants = fq_constants();

    {
        let start = std::time::Instant::now();
        // Defining global parameters and performing one-time setup

        let brave_sk = <Other as AffineCurve>::ScalarField::rand(&mut rand_core::OsRng);
        let brave_pubkey = Other::prime_subgroup_generator()
            .mul(brave_sk)
            .into_affine();

        let bba = bba::Params::new(&other_srs, endo_r);

        let h = other_srs.h.to_coordinates().unwrap();
        let init_params = bba_init_proof::Params {
            l0: bba.lagrange_commitments[0].to_coordinates().unwrap(),
            h,
        };

        let update_params = bba_update_proof::Params {
            brave_pubkey: brave_pubkey.to_coordinates().unwrap(),
            h,
        };

        let fq_poseidon = oracle::pasta::fq5::params();
        let fp_poseidon = oracle::pasta::fp5::params();

        let init_pk = generate_proving_key::<FpInner, _>(
            &srs,
            &proof_system_constants,
            &fq_poseidon,
            2,
            |sys, p| bba_init_proof::circuit::<_, Other, _>(&init_params, &None, sys, p),
        );
        let init_vk = init_pk.verifier_index();

        let update_pk = generate_proving_key::<FpInner, _>(
            &srs,
            &proof_system_constants,
            &fq_poseidon,
            2,
            |sys, p| {
                bba_update_proof::circuit::<_, Other, _>(
                    &proof_system_constants,
                    &update_params,
                    &None,
                    sys,
                    p,
                )
            },
        );
        let update_vk = update_pk.verifier_index();

        let open_params = bba_open_proof::Params {
            // The public vector of prices-per-view for the campaigns
            prices: (0..bba::MAX_COUNTERS)
                .map(|i| {
                    let i = i as u32;
                    i * i + 1
                })
                .collect(),
        };

        let open_pk = generate_proving_key::<FqInner, _>(
            &other_srs,
            &fq_proof_system_constants,
            &fp_poseidon,
            2,
            |sys, p| bba_open_proof::circuit::<_, Affine, _>(&open_params, &None, sys, p),
        );
        let open_vk = open_pk.verifier_index();

        let other_lgr_comms: Vec<PolyComm<Affine>> = fft::lagrange_commitments(&srs)
            .iter()
            .map(|g| PolyComm {
                unshifted: vec![*g],
                shifted: None,
            })
            .collect();

        // End of setup
        println!(
            "Parameter precomputation (one time cost) ({:?})\n",
            start.elapsed()
        );

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
                g_group_map: g_group_map.clone(),
                open_pk,
                open_params: open_params.clone(),
                proof_system_constants: proof_system_constants.clone(),
                init_params: init_params.clone(),
                update_params: update_params.clone(),
                init_pk,
                update_pk,
            },
        };

        // First, the user requests an initial BBA from the authority
        let init_secrets = bba::init_secrets();
        let init_request = time("User:      Create BBA init request", || {
            user_config.request_init::<SpongeQ, SpongeR>(init_secrets)
        });

        // Then, the authority responds with an initial BBA.
        let init_signature = time("Authority: Sign initial accumulator", || {
            update_authority
                .perform_init::<SpongeQ, SpongeR>(init_request.clone())
                .unwrap()
        });

        let mut user =
            bba::User::<FpInner>::init(user_config, init_secrets, init_signature).unwrap();

        // Then, the user can request to perform an update by incrementing views in some campaigns
        let updates = (0..1000)
            .map(|i| bba::SingleUpdate {
                campaign_index: i,
                delta: 10 * (i + 1),
            })
            .collect();
        let update_request = time("User:      Create BBA update request", || {
            user.request_update::<SpongeQ, SpongeR>(updates)
        });

        // and the authority can validate the unlinkable update request and provide an updated BBA
        let resp = time("Authority: Update BBA", || {
            update_authority.perform_updates::<SpongeQ, SpongeR>(vec![update_request.clone()])[0]
                .as_ref()
                .unwrap()
                .clone()
        });
        time("User:      Process update response", || {
            user.process_update_response(&update_request.updates, &resp)
        });

        // Now, the user can open their BBA to a reward in a zero-knowledge way
        let opening = time("User:      Open BBA", || user.open::<PSpongeQ, PSpongeR>());
        let opening_size = bba::proof_size(&opening.proof);
        // Finally, we can verify the correctness of the opening
        let _payout = opening
            .verify::<PSpongeQ, PSpongeR>(&signer, &bba, brave_pubkey, &g_group_map, &open_vk)
            .unwrap();

        println!("------------------------------");
        println!("Init proof size:    {} bytes", bba::proof_size(&init_request.proof));
        println!("Update proof size:  {} bytes", bba::proof_size(&update_request.proof));
        println!("Opening proof size: {} bytes", opening_size);
    }
}
