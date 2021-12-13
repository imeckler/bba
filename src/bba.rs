use rayon::prelude::*;
use crate::bba_init_proof;
use crate::bba_open_proof;
use crate::bba_update_proof;
use crate::endo::EndoScalar;
use crate::fft::lagrange_commitments;
use crate::proof_system;
use crate::schnorr;
use algebra::{AffineCurve, PrimeField, ProjectiveCurve, UniformRand, VariableBaseMSM, Zero};
use array_init::array_init;
use commitment_dlog::{
    commitment::{CommitmentCurve, PolyComm},
    srs::SRS,
};
use oracle::FqSponge;
use plonk_protocol_dlog::{
    index::{Index, VerifierIndex},
    plonk_sponge::FrSponge,
    prover::ProverProof,
};
use schnorr::SignatureParams;

#[derive(Clone)]
pub struct Params<G: AffineCurve> {
    pub h: G,
    pub endo: G::ScalarField,
    pub lagrange_commitments: Vec<G>,
}

pub struct Randomized<G: AffineCurve> {
    pub result: G,
    pub witness: EndoScalar<G::ScalarField>,
}

pub const COUNTER_OFFSET: usize = bba_open_proof::PUBLIC_INPUT + proof_system::ZK_ROWS;
pub const MAX_COUNTERS: usize =
    (1 << 10) - bba_open_proof::PUBLIC_INPUT - proof_system::ZK_ROWS - 3;

impl<G: AffineCurve> Params<G> {
    pub fn randomize(&self, p: G) -> Randomized<G> {
        let rng = &mut rand_core::OsRng;
        let r = EndoScalar(G::ScalarField::rand(rng));
        let mask = self.h.mul(r.to_field(&self.endo));
        let result = (p.into_projective() + &mask).into_affine();
        Randomized { result, witness: r }
    }

    pub fn secret_commitment(&self, secrets: &bba_init_proof::Witness<G>) -> G {
        let lg = &self.lagrange_commitments;
        let bases = vec![self.h, lg[0], lg[2], lg[3], lg[4], lg[5], lg[6]];
        let scalars = vec![
            secrets.r,
            secrets.c,
            secrets.alpha[0],
            secrets.alpha[1],
            secrets.alpha[2],
            secrets.alpha[3],
            secrets.alpha[4],
        ];
        let scalars: Vec<_> = scalars.iter().map(|x| x.into_repr()).collect();
        VariableBaseMSM::multi_scalar_mul(bases.as_slice(), scalars.as_slice()).into_affine()
    }
}

#[derive(Copy, Clone)]
pub struct SingleUpdate {
    pub campaign_index: u32,
    pub delta: u32,
}

// The request sent by a user to the server to get an initial BBA
#[derive(Clone)]
pub struct InitRequest<G: AffineCurve, Other: AffineCurve> {
    acc: G,
    // A proof of:
    // I know r, c such that acc = r * H + c * L.
    // Could be replaced with a specialized schnorr proof for increased efficiency
    pub proof: ProverProof<Other>,
}

// The request sent by a user to the server to get a signed, updated BBA
#[derive(Clone)]
pub struct UpdateRequest<G: AffineCurve, Other: AffineCurve> {
    pub updates: Vec<SingleUpdate>,
    // A proof of:
    // I know a valid signature on a value [acc], and [r] such that [acc = r H]
    pub proof: ProverProof<Other>,
    randomized_acc: G,
}

// size in bytes
pub fn proof_size<G: CommitmentCurve>(proof: &ProverProof<G>) -> usize {
    fn poly_comm<A>(pc: &PolyComm<A>) -> usize {
        match &pc.shifted {
            None => pc.unshifted.len(),
            Some(_) => 1 + pc.unshifted.len(),
        }
    }

    let mut group_elt_count = 0;
    let mut field_elt_count = 0;
    group_elt_count += poly_comm(&proof.commitments.z_comm);
    group_elt_count += poly_comm(&proof.commitments.t_comm);
    for w in proof.commitments.w_comm.iter() {
        group_elt_count += poly_comm(w);
    }

    // opening proof
    group_elt_count += 2;
    group_elt_count += proof.proof.lr.len() * 2;
    field_elt_count += 2;

    // evaluations
    for e in proof.evals.iter() {
        field_elt_count += e.z.len();
        field_elt_count += e.t.len();
        field_elt_count += e.f.len();
        for v in e.w.iter() {
            field_elt_count += v.len();
        }
        for v in e.s.iter() {
            field_elt_count += v.len();
        }
    }

    32 * (group_elt_count + field_elt_count) + ((group_elt_count + 7) / 8)
}

// No need to send the actual updated accumulator as the user can compute
// that themselves.
#[derive(Clone)]
pub struct UpdateResponse<G: AffineCurve> {
    signature: schnorr::Signature<G>,
}

pub struct UpdateAuthority<'a, G: schnorr::CoordinateCurve, Other: CommitmentCurve> {
    pub signing_key: schnorr::PrivateKey<G>,
    pub signer: schnorr::Signer<G>,
    pub lgr_comms: Vec<G>,
    pub update_vk: VerifierIndex<'a, Other>,
    pub init_vk: VerifierIndex<'a, Other>,
    pub other_lgr_comms: Vec<PolyComm<Other>>,
    pub big_other_lgr_comms: Vec<PolyComm<Other>>,
    pub group_map: Other::Map,
}

pub struct UserProver<'a, G: CommitmentCurve, Other: CommitmentCurve> {
    pub proof_system_constants: proof_system::Constants<Other::ScalarField>,
    pub group_map: Other::Map,
    pub g_group_map: G::Map,
    pub init_pk: Index<'a, Other>,
    pub update_pk: Index<'a, Other>,
    pub open_pk: Index<'a, G>,
    pub update_params: bba_update_proof::Params<Other::ScalarField>,
    pub init_params: bba_init_proof::Params<G>,
    pub open_params: bba_open_proof::Params,
}

pub struct UserConfig<'a, G: CommitmentCurve, Other: CommitmentCurve> {
    pub signer: schnorr::Signer<G>,
    pub authority_public_key: schnorr::PublicKey<G>,
    pub bba: Params<G>,
    pub prover: UserProver<'a, G, Other>,
}

pub struct UserState<G: CommitmentCurve> {
    // Invariant: [signature] verifies on the message [acc + h.mul(r)] against
    // [authority_public_key]
    pub r: G::ScalarField,
    pub c: G::ScalarField,
    pub alpha: [G::ScalarField; proof_system::ZK_ROWS],
    pub counters: Vec<u32>,
    pub acc: G,
    pub signature: schnorr::Signature<G>,
    pub pending_update_witness: Option<Randomized<G>>,
}

pub struct User<'a, C: proof_system::Cycle> {
    //    G: CommitmentCurve, Other: CommitmentCurve
    pub config: UserConfig<'a, C::Inner, C::Outer>,
    pub state: UserState<C::Inner>,
}

pub struct RewardOpening<C: proof_system::Cycle> {
    pub proof: ProverProof<C::Inner>,
    pub signature: schnorr::Signature<C::Inner>,
}

pub struct Payout<C: proof_system::Cycle> {
    pub amount: u64,
    pub nullifier: C::OuterField,
}

impl<C: proof_system::Cycle> RewardOpening<C> {
    pub fn verify_batch<
        'a,
        EFqSponge: Clone + FqSponge<C::InnerField, C::Inner, C::OuterField>,
        EFrSponge: FrSponge<C::OuterField>,
    >(
        signer: &schnorr::Signer<C::Inner>,
        bba: &Params<C::Inner>,
        authority_public_key: C::Inner,
        group_map: &C::InnerMap,
        vk: &VerifierIndex<'a, C::Inner>,
        openings: Vec<&Self>
    ) -> Result<(), String> {
        let lgr_comms: Vec<PolyComm<_>> = bba
            .lagrange_commitments
            .iter()
            .map(|g| PolyComm {
                unshifted: vec![*g],
                shifted: None,
            })
            .collect();
        let batch : Vec<_> = openings.iter().map(|x| (vk, &lgr_comms, &x.proof)).collect();
        match ProverProof::verify::<EFqSponge, EFrSponge>(
            &group_map,
            &batch
        ) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err("Open proof failed to verify"),
        }?;

        for opening in openings.iter() {
            let amount = opening.proof.public[1];

            let acc = opening.proof.commitments.w_comm[0].unshifted[0].into_projective()
                - &bba.lagrange_commitments[1].mul(amount);

            if !signer.verify(authority_public_key, acc.into(), opening.signature) {
                return Err(String::from("Open signature failed to verify"));
            }
        }

        return Ok(());
    }

    pub fn verify<
        'a,
        EFqSponge: Clone + FqSponge<C::InnerField, C::Inner, C::OuterField>,
        EFrSponge: FrSponge<C::OuterField>,
    >(
        &self,
        signer: &schnorr::Signer<C::Inner>,
        bba: &Params<C::Inner>,
        authority_public_key: C::Inner,
        group_map: &C::InnerMap,
        vk: &VerifierIndex<'a, C::Inner>,
    ) -> Result<Payout<C>, &str> {
        let lgr_comms: Vec<PolyComm<_>> = bba
            .lagrange_commitments
            .iter()
            .map(|g| PolyComm {
                unshifted: vec![*g],
                shifted: None,
            })
            .collect();
        match ProverProof::verify::<EFqSponge, EFrSponge>(
            &group_map,
            &vec![(vk, &lgr_comms, &self.proof)],
        ) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err("Open proof failed to verify"),
        }?;

        let amount = self.proof.public[1];

        let acc = self.proof.commitments.w_comm[0].unshifted[0].into_projective()
            - &bba.lagrange_commitments[1].mul(amount);

        if !signer.verify(authority_public_key, acc.into(), self.signature) {
            return Err("Open signature failed to verify");
        }

        let nullifier = self.proof.public[0];
        let amount = amount.into_repr();
        let a = amount.as_ref();

        for i in 1..a.len() {
            assert_eq!(a[i], 0)
        }
        let amount = a[0];

        Ok(Payout { amount, nullifier })
    }
}

fn update_delta<G: AffineCurve>(
    lagrange_commitments: &[G],
    updates: &[SingleUpdate],
) -> G::Projective {
    let bases: Vec<G> = updates
        .iter()
        .map(|u| {
            // The first N lagrange commitments are reserved for public input
            lagrange_commitments[COUNTER_OFFSET + u.campaign_index as usize]
        })
        .collect();
    let scalars: Vec<<G::ScalarField as PrimeField>::BigInt> =
        updates.iter().map(|u| (u.delta as u64).into()).collect();

    VariableBaseMSM::multi_scalar_mul(bases.as_slice(), scalars.as_slice())
}

pub fn init_secrets<G: AffineCurve>() -> bba_init_proof::Witness<G> {
    let rng = &mut rand_core::OsRng;
    bba_init_proof::Witness {
        r: G::ScalarField::rand(rng),
        c: G::ScalarField::rand(rng),
        alpha: array_init(|_| G::ScalarField::rand(rng)),
    }
}

impl<'a, C: proof_system::Cycle> User<'a, C> {
    pub fn check_invariant(&self) {
        let reward = self
            .state
            .counters
            .iter()
            .zip(self.config.prover.open_params.prices.iter())
            .fold(C::OuterField::zero(), |acc, (x, y)| {
                acc + &((*x as u64) * (*y as u64)).into()
            });

        let mut bases: Vec<_> = self.config.bba.lagrange_commitments.clone();
        bases.push(self.config.bba.h);

        let mut scalars = vec![self.state.c.into_repr(), reward.into_repr()];
        // let mut scalars : Vec<<C::OuterField as PrimeField>::BigInt> =
        scalars.extend(
            self.state
                .counters
                .iter()
                .map(|u| -> <C::OuterField as PrimeField>::BigInt { (*u as u64).into() })
                .collect::<Vec<_>>(),
        );
        scalars.extend(vec![
            C::OuterField::zero().into_repr();
            proof_system::ZK_ROWS
        ]);
        scalars.push(self.state.r.into_repr());

        assert_eq!(scalars.len(), bases.len());
        assert_eq!(
            VariableBaseMSM::multi_scalar_mul(bases.as_slice(), scalars.as_slice()).into_affine(),
            self.state.acc + self.config.bba.lagrange_commitments[1].mul(reward).into()
        );
    }

    pub fn init(
        config: UserConfig<'a, C::Inner, C::Outer>,
        secrets: bba_init_proof::Witness<C::Inner>,
        signature: schnorr::Signature<C::Inner>,
    ) -> Result<Self, &str> {
        let acc = config.bba.secret_commitment(&secrets);

        if !config
            .signer
            .verify(config.authority_public_key, acc, signature)
        {
            return Err("init signature failed to verify");
        }

        let counters = vec![0; MAX_COUNTERS];
        Ok(User {
            config,
            state: UserState {
                r: secrets.r,
                c: secrets.c,
                alpha: secrets.alpha,
                acc: acc,
                counters,
                signature,
                pending_update_witness: None,
            },
        })
    }

    pub fn open<
        EFqSponge: Clone + FqSponge<C::InnerField, C::Inner, C::OuterField>,
        EFrSponge: FrSponge<C::OuterField>,
    >(
        self,
    ) -> RewardOpening<C> {
        let config = &self.config;
        let reward = self
            .state
            .counters
            .iter()
            .zip(config.prover.open_params.prices.iter())
            .fold(C::OuterField::zero(), |acc, (x, y)| {
                acc + &((*x as u64) * (*y as u64)).into()
            });
        let w = bba_open_proof::Witness {
            counters: self.state.counters.clone(),
            alpha: self.state.alpha.clone(),
        };
        let proof = proof_system::prove::<C::Inner, _, EFqSponge, EFrSponge>(
            &config.prover.open_pk,
            &config.prover.g_group_map,
            Some([Some(self.state.r), None, None, None, None]),
            vec![self.state.c, reward],
            |sys, p| {
                bba_open_proof::circuit::<C::OuterField, C::Outer, _>(
                    &config.prover.open_params,
                    &Some(w),
                    sys,
                    p,
                )
            },
        );
        RewardOpening {
            proof,
            signature: self.state.signature,
        }
    }

    pub fn process_update_response(
        &mut self,
        updates: &Vec<SingleUpdate>,
        resp: &UpdateResponse<C::Inner>,
    ) {
        let state = &mut self.state;
        let config = &self.config;
        match state.pending_update_witness {
            None => {
                eprintln!("Unexpected update response");
            }
            Some(Randomized {
                result: randomized_acc,
                witness: r,
            }) => {
                assert_eq!(
                    randomized_acc,
                    state.acc + config.bba.h.mul(r.to_field(&config.bba.endo)).into_affine()
                );
                let updated_acc = update_delta(
                    self.config.bba.lagrange_commitments.as_slice(),
                    updates.as_slice(),
                )
                .add_mixed(&randomized_acc)
                .into_affine();

                if config
                    .signer
                    .verify(config.authority_public_key, updated_acc, resp.signature)
                {
                    state.pending_update_witness = None;
                    state.acc = updated_acc;
                    state.signature = resp.signature;
                    state.r += &r.to_field(&config.bba.endo);

                    for SingleUpdate {
                        campaign_index,
                        delta,
                    } in updates.iter()
                    {
                        state.counters[*campaign_index as usize] += delta;
                    }
                } else {
                    eprintln!("Received invalid signature from update authority");
                }
            }
        }
    }
}

impl<'a, G: CommitmentCurve, Other: CommitmentCurve<ScalarField = G::BaseField>>
    UserConfig<'a, G, Other>
where
    G::BaseField: algebra::SquareRootField + algebra::PrimeField,
    <Other as algebra::curves::AffineCurve>::Projective:
        std::ops::MulAssign<<G as algebra::curves::AffineCurve>::BaseField>,
{
    pub fn request_init<
        EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>,
        EFrSponge: FrSponge<Other::ScalarField>,
    >(
        &self,
        secrets: bba_init_proof::Witness<G>,
    ) -> InitRequest<G, Other> {
        let acc = self.bba.secret_commitment(&secrets);
        let (acc_x, acc_y) = acc.to_coordinates().unwrap();

        let proof = proof_system::prove::<Other, _, EFqSponge, EFrSponge>(
            &self.prover.init_pk,
            &self.prover.group_map,
            None,
            vec![acc_x, acc_y],
            |sys, p| {
                bba_init_proof::circuit::<_, G, _>(&self.prover.init_params, &Some(secrets), sys, p)
            },
        );
        InitRequest { acc, proof }
    }
}

impl<'a, C: proof_system::Cycle> User<'a, C> {
    pub fn request_update<
        EFqSponge: Clone + FqSponge<C::OuterField, C::Outer, C::InnerField>,
        EFrSponge: FrSponge<C::InnerField>,
    >(
        &mut self,
        updates: Vec<SingleUpdate>,
    ) -> UpdateRequest<C::Inner, C::Outer> {
        let config = &self.config;
        let state = &self.state;
        let randomization_witness = config.bba.randomize(state.acc);
        let witness = bba_update_proof::Witness {
            acc: state.acc,
            signature: state.signature,
            r: randomization_witness.witness.0,
        };
        let new_acc = randomization_witness.result;
        let (new_acc_x, new_acc_y) = new_acc.to_coordinates().unwrap();
        let proof = proof_system::prove::<C::Outer, _, EFqSponge, EFrSponge>(
            &config.prover.update_pk,
            &config.prover.group_map,
            None,
            vec![new_acc_x, new_acc_y],
            |sys, p| {
                bba_update_proof::circuit(
                    &config.prover.proof_system_constants,
                    &config.prover.update_params,
                    &Some(witness),
                    sys,
                    p,
                )
            },
        );
        self.state.pending_update_witness = Some(randomization_witness);
        UpdateRequest {
            updates,
            proof,
            randomized_acc: new_acc,
        }
    }
}

// In production this should be more async
fn batch_verify<V, A: Clone>(verify: &V, xs: Vec<A>) -> Vec<bool>
where
    V: Fn(&Vec<A>) -> bool,
{
    if verify(&xs) {
        xs.iter().map(|_| true).collect()
    } else {
        if xs.len() == 1 {
            return vec![false];
        } else {
            let n = xs.len();
            let n_l = n / 2;
            let l = (&xs[..n_l]).to_vec();
            let r = (&xs[n_l..]).to_vec();
            let mut l = batch_verify(verify, l);
            l.extend(batch_verify(verify, r));
            l
        }
    }
}

fn batch_verify_proofs<
    G: CommitmentCurve,
    EFqSponge: Clone + FqSponge<G::BaseField, G, G::ScalarField>,
    EFrSponge: FrSponge<G::ScalarField>,
>(
    group_map: &G::Map,
    proofs: Vec<(&VerifierIndex<G>, &Vec<PolyComm<G>>, &ProverProof<G>)>,
) -> Vec<bool> {
    let verify = |ps: &Vec<_>| match ProverProof::verify::<EFqSponge, EFrSponge>(group_map, ps) {
        Ok(true) => true,
        Ok(false) => false,
        Err(_) => false,
    };
    batch_verify(&verify, proofs)
}

// This code would run on brave's server for instance
impl<'a, G: CommitmentCurve, Other: CommitmentCurve<ScalarField = G::BaseField>>
    UpdateAuthority<'a, G, Other>
where
    G::BaseField: algebra::SquareRootField + algebra::PrimeField,
    <Other as algebra::curves::AffineCurve>::Projective:
        std::ops::MulAssign<<G as algebra::curves::AffineCurve>::BaseField>,
{
    pub fn perform_init<
        EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>,
        EFrSponge: FrSponge<Other::ScalarField>,
    >(
        &self,
        mut req: InitRequest<G, Other>,
    ) -> Result<schnorr::Signature<G>, &str> {
        let acc = match req.acc.to_coordinates() {
            None => Err("Init bad acc"),
            Some(p) => Ok(p),
        }?;
        req.proof.public = vec![acc.0, acc.1];
        match ProverProof::verify::<EFqSponge, EFrSponge>(
            &self.group_map,
            &vec![(&self.init_vk, &self.big_other_lgr_comms, &req.proof)],
        ) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err("Init proof failed to verify"),
        }?;
        Ok(self.signer.sign(self.signing_key, req.acc))
    }

    pub fn batch_init<
        EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>,
        EFrSponge: FrSponge<Other::ScalarField>,
    >(
        &self,
        mut reqs: Vec<InitRequest<G, Other>>,
    ) -> Result<Vec<schnorr::Signature<G>>, &str> {
        for req in reqs.iter_mut() {
            let acc = match req.acc.to_coordinates() {
                None => Err("Init bad acc"),
                Some(p) => Ok(p),
            }?;
            req.proof.public = vec![acc.0, acc.1];
        }

        let batch : Vec<_> = reqs.iter().map(|r| (&self.init_vk, &self.big_other_lgr_comms, &r.proof)).collect();

        match ProverProof::verify::<EFqSponge, EFrSponge>(
            &self.group_map,
            &batch,
        ) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err("Init proofs failed to verify"),
        }?;
        let accs : Vec<_> = reqs.iter().map(|r| r.acc).collect();
        let signing_key = self.signing_key.clone();
        let signer = self.signer.clone();
        let res : Vec<_> = accs.par_iter().map(|acc| {
            signer.sign(signing_key, *acc)
        }).collect();
        Ok(res)
    }

    // This function is batched for efficiency of proof verification
    pub fn perform_updates<
        EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>,
        EFrSponge: FrSponge<Other::ScalarField>,
    >(
        &self,
        mut reqs: Vec<UpdateRequest<G, Other>>,
    ) -> Vec<Result<UpdateResponse<G>, &str>> {
        let mut results = vec![Err(""); reqs.len()];

        let mut batch_indices = vec![];
        let mut batch = vec![];
        for (i, req) in reqs.iter_mut().enumerate() {
            match req.randomized_acc.to_coordinates() {
                None => results[i] = Err("Invalid accumulator in request"),
                Some((x, y)) => {
                    req.proof.public = vec![x, y];
                    batch_indices.push(i);
                    batch.push((&self.update_vk, &self.other_lgr_comms, &req.proof))
                }
            }
        }

        let mut success_indices = vec![];
        let verify_results = batch_verify_proofs::<_, EFqSponge, EFrSponge>(&self.group_map, batch);
        for (&i, verified) in batch_indices.iter().zip(verify_results) {
            if verified {
                success_indices.push(i);
            } else {
                results[i] = Err("Update proof failed to verify");
            }
        }

        for i in success_indices {
            let req = &reqs[i];

            let delta = update_delta(&self.lgr_comms[..], &req.updates[..]);

            let new_acc = delta.add_mixed(&req.randomized_acc).into_affine();

            results[i] = Ok(UpdateResponse::<G> {
                signature: self.signer.sign(self.signing_key, new_acc),
            });
        }

        results
    }
}

impl<G: CommitmentCurve> Params<G> {
    pub fn new(srs: &SRS<G>, endo: G::ScalarField) -> Params<G> {
        Params {
            h: srs.h,
            endo,
            lagrange_commitments: lagrange_commitments(srs),
        }
    }
}
