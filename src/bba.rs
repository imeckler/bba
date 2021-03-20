use algebra::{AffineCurve, ProjectiveCurve, UniformRand, VariableBaseMSM, PrimeField};
use crate::schnorr;
use crate::endo::EndoScalar;
use crate::fft::lagrange_commitments;
use commitment_dlog::{srs::SRS, commitment::{PolyComm, CommitmentCurve, CommitmentField}};
use plonk_5_wires_protocol_dlog::{prover::{ProverProof}, index::{Index, VerifierIndex}, plonk_sponge::{FrSponge}};
use oracle::FqSponge;
use schnorr::SignatureParams;
use crate::util::*;
use crate::proof_system;
use crate::bba_init_proof;
use crate::bba_update_proof;
use crate::bba_open_proof;

#[derive(Clone)]
pub struct Params<G : AffineCurve> {
    pub h: G,
    pub endo: G::ScalarField,
    pub lagrange_commitments: Vec<G>
}

pub struct Randomized<G: AffineCurve> {
    pub result: G,
    pub witness: EndoScalar<G::ScalarField>
}

pub const MAX_COUNTERS : usize = (1 << 10) - bba_open_proof::PUBLIC_INPUT - proof_system::ZK_ROWS;

impl<G:AffineCurve> Params<G> {
    pub fn randomize(&self, p : G) -> Randomized<G> {
        let rng = &mut rand_core::OsRng;
        let r = EndoScalar(G::ScalarField::rand(rng));
        let mask = self.h.mul(r.to_field(&self.endo));
        let result = (p.into_projective() + &mask).into_affine();
        Randomized {
            result,
            witness:r 
        }
    }
}

#[derive(Copy, Clone)]
pub struct SingleUpdate {
    campaign_index: u32,
    delta: u32
}

// The request sent by a user to the server to get an initial BBA
#[derive(Clone)]
pub struct InitRequest<G: AffineCurve, Other: AffineCurve> {
    acc: G,
    // A proof of:
    // I know r, c such that acc = r * H + c * L.
    // Could be replaced with a specialized schnorr proof for increased efficiency
    proof: ProverProof<Other>,
}

// The request sent by a user to the server to get a signed, updated BBA
#[derive(Clone)]
pub struct UpdateRequest<G: AffineCurve, Other: AffineCurve> {
    updates: Vec<SingleUpdate>,
    // A proof of:
    // I know a valid signature on a value [acc], and [r] such that [acc = r H]
    proof: ProverProof<Other>,
    randomized_acc: G
}

// No need to send the actual updated accumulator as the user can compute
// that themselves.
#[derive(Clone)]
pub struct UpdateResponse<G: AffineCurve> {
    signature: schnorr::Signature<G>
}

pub struct UpdateAuthority<'a, G: schnorr::CoordinateCurve, Other: CommitmentCurve> {
    pub signing_key: schnorr::PrivateKey<G>,
    pub signer: schnorr::Signer<G>,
    pub lgr_comms: Vec<G>,
    pub update_vk: VerifierIndex<'a, Other>,
    pub init_vk: VerifierIndex<'a, Other>,
    pub other_lgr_comms: Vec<PolyComm<Other>>,
    pub group_map: Other::Map,
}

pub struct UserProver<'a, Other:CommitmentCurve> {
    pub proof_system_constants: proof_system::Constants<Other::ScalarField>,
    pub group_map: Other::Map,
    pub update_pk: Index<'a, Other>,
    pub init_pk: Index<'a, Other>,
    pub update_params: bba_update_proof::Params<Other::ScalarField>,
    pub init_params: bba_init_proof::Params<Other::ScalarField>,
}

pub struct UserConfig<'a, G: CommitmentCurve, Other: CommitmentCurve> {
    pub signer: schnorr::Signer<G>,
    pub authority_public_key: schnorr::PublicKey<G>,
    pub bba: Params<G>,
    pub prover: UserProver<'a, Other>,
}

pub struct UserState<G: CommitmentCurve>
{
    // Invariant: [signature] verifies on the message [acc + h.mul(r)] against
    // [authority_public_key]
    pub r: G::ScalarField,
    pub c: G::ScalarField,
    pub counters: Vec<u32>,
    pub acc: G,
    pub signature: schnorr::Signature<G>,
    pub pending_update_witness: Option<Randomized<G>>
}

pub struct User<'a, G: CommitmentCurve, Other: CommitmentCurve> {
    config: UserConfig<'a, G, Other>,
    state: UserState<G>
}

type Error = String;

fn update_delta<G : AffineCurve>(
    lagrange_commitments: &[G],
    updates: &[SingleUpdate]) -> G::Projective {
    let bases : Vec<G> = updates.iter().map(|u| {
        // The first N lagrange commitments are reserved for public input
        lagrange_commitments[bba_open_proof::PUBLIC_INPUT + u.campaign_index as usize]
    }).collect();
    let scalars : Vec<<G::ScalarField as PrimeField>::BigInt> = 
        updates.iter().map(|u| (u.delta as u64).into()).collect();

    VariableBaseMSM::multi_scalar_mul(bases.as_slice(), scalars.as_slice())
}

pub fn init_secrets<G:AffineCurve>() -> bba_init_proof::Witness<G> {
    let rng = &mut rand_core::OsRng;
    bba_init_proof::Witness {
        r: G::ScalarField::rand(rng),
        c: G::ScalarField::rand(rng)
    }
}

impl<'a, G: CommitmentCurve, Other: CommitmentCurve> User<'a, G, Other> where G::BaseField : PrimeField {
    pub fn init(config : UserConfig<'a, G, Other>, secrets: bba_init_proof::Witness<G>, signature: schnorr::Signature<G>) -> Self {
        let acc = config.bba.h.mul(secrets.r) + &config.bba.lagrange_commitments[0].mul(secrets.c);
        let counters = vec![0; MAX_COUNTERS];
        User {
            config,
            state: UserState {
                r: secrets.r,
                c: secrets.c,
                acc: acc.into_affine(),
                counters,
                signature,
                pending_update_witness: None
            }
        }
    }

    pub fn process_update_response(
        &mut self,
        updates: &Vec<SingleUpdate>, 
        resp: UpdateResponse<G> ) {
        let state = &mut self.state;
        let config = &self.config;
        match state.pending_update_witness {
            None => {
                eprintln!("Unexpected update response");
            },
            Some(Randomized { result: randomized_acc, witness: r}) => {
                let updated_acc =
                    update_delta(self.config.bba.lagrange_commitments.as_slice(), updates.as_slice())
                    .add_mixed(&randomized_acc).into_affine();

                if config.signer.verify(config.authority_public_key, updated_acc, resp.signature) {
                    state.pending_update_witness = None;
                    state.acc = updated_acc;
                    state.signature = resp.signature;
                    state.r += &r.to_field(&config.bba.endo);

                    for SingleUpdate { campaign_index, delta } in updates.iter() {
                        state.counters[*campaign_index as usize] += delta;
                    }
                } else {
                    eprintln!("Received invalid signature from update authority");
                }
            }
        }
    }
}

impl<'a, G: CommitmentCurve, Other: CommitmentCurve<ScalarField=G::BaseField>> UserConfig<'a, G, Other> 
where G::BaseField: algebra::SquareRootField + algebra::PrimeField,
      G::ScalarField : CommitmentField,
      G::BaseField : CommitmentField,
      <Other as algebra::curves::AffineCurve>::Projective: std::ops::MulAssign<<G as algebra::curves::AffineCurve>::BaseField>
{
    pub fn request_init<EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>, EFrSponge: FrSponge<Other::ScalarField>>(
        &self,
        secrets: bba_init_proof::Witness<G>) -> InitRequest<G, Other> 
    {
        let acc = self.bba.h.mul(secrets.r) + &self.bba.lagrange_commitments[0].mul(secrets.c);
        let acc = acc.into_affine();
        let (acc_x, acc_y) = acc.to_coordinates().unwrap();

        let proof = time("init proving time", ||
            proof_system::prove::<Other, _, EFqSponge, EFrSponge>(
                &self.prover.init_pk, 
                &self.prover.group_map, vec![acc_x, acc_y], |sys, p| {
                bba_init_proof::circuit(
                    &self.prover.init_params, &Some(secrets), sys, p)
            }));
        InitRequest {
            acc,
            proof
        }
    }
}

impl<'a, G: CommitmentCurve, Other: CommitmentCurve<ScalarField=G::BaseField>> User<'a, G, Other> 
where G::BaseField: algebra::SquareRootField + algebra::PrimeField,
      G::ScalarField : CommitmentField,
      G::BaseField : CommitmentField,
      <Other as algebra::curves::AffineCurve>::Projective: std::ops::MulAssign<<G as algebra::curves::AffineCurve>::BaseField>
{
    pub fn request_update<EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>, EFrSponge: FrSponge<Other::ScalarField>>(
        &mut self,
        updates: Vec<SingleUpdate>) -> UpdateRequest<G, Other> 
    {
        let config = &self.config;
        let state = &mut self.state;
        let randomization_witness  = config.bba.randomize(state.acc);
        let witness = bba_update_proof::Witness {
            acc: state.acc,
            signature: state.signature,
            r: randomization_witness.witness.0
        };
        let new_acc = randomization_witness.result;
        let (new_acc_x, new_acc_y) = new_acc.to_coordinates().unwrap();
        let proof = time("update proving time", ||
            proof_system::prove::<Other, _, EFqSponge, EFrSponge>(
                &config.prover.update_pk, 
                &config.prover.group_map, vec![new_acc_x, new_acc_y], |sys, p| {
                bba_update_proof::circuit(
                    &config.prover.proof_system_constants,
                    &config.prover.update_params, &Some(witness), sys, p)
            }));
        state.pending_update_witness = Some(randomization_witness);
        UpdateRequest {
            updates,
            proof,
            randomized_acc: new_acc
        }
    }
}

// In production this should be more async
fn batch_verify<V, A: Clone>(verify: &V, xs: Vec<A>) -> Vec<bool> where V: Fn(&Vec<A>) -> bool {
    if verify(&xs) {
        xs.iter().map(|_| true).collect()
    } else {
        if xs.len() == 1 {
            return vec![false]
        } else {
            let n = xs.len();
            let n_l = n / 2;
            let l =(&xs[..n_l]).to_vec();
            let r =(&xs[n_l..]).to_vec();
            let mut l = batch_verify(verify, l);
            l.extend(batch_verify(verify, r));
            l
        }
    }
}

fn batch_verify_proofs<G: CommitmentCurve, EFqSponge: Clone + FqSponge<G::BaseField, G, G::ScalarField>, EFrSponge: FrSponge<G::ScalarField>>
(group_map: &G::Map, 
proofs: Vec<(&VerifierIndex<G>, &Vec<PolyComm<G>>, &ProverProof<G>)>) -> Vec<bool>
where G::ScalarField : CommitmentField
{
    let verify = |ps : &Vec<_>| {
        match ProverProof::verify::<EFqSponge, EFrSponge>(group_map, ps) {
            Ok(true) => true,
            Ok(false) => false,
            Err(_) => false
        }
    };
    batch_verify(&verify, proofs)
}

// This code would run on brave's server for instance
impl<'a, G: CommitmentCurve, Other: CommitmentCurve<ScalarField=G::BaseField>> UpdateAuthority<'a, G, Other> 
where G::BaseField: algebra::SquareRootField + algebra::PrimeField,
      G::ScalarField : CommitmentField,
      G::BaseField : CommitmentField,
      <Other as algebra::curves::AffineCurve>::Projective: std::ops::MulAssign<<G as algebra::curves::AffineCurve>::BaseField>
{
    pub fn perform_init<EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>, EFrSponge: FrSponge<Other::ScalarField>>(
        &self,
        mut req: InitRequest<G, Other>
        ) -> Result<schnorr::Signature<G>, &str> {
        let acc =
            match req.acc.to_coordinates() {
                None => Err("Init bad acc"),
                Some(p) => Ok(p)
            }?;
        req.proof.public = vec![acc.0, acc.1];
        match ProverProof::verify::<EFqSponge, EFrSponge>(&self.group_map, &vec![(&self.init_vk, &self.other_lgr_comms, &req.proof)]) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err("Init proof failed to verify"),
        }?;
        Ok(self.signer.sign(self.signing_key, req.acc))
    }

    // This function is batched for efficiency of proof verification
    pub fn perform_updates<EFqSponge: Clone + FqSponge<Other::BaseField, Other, Other::ScalarField>, EFrSponge: FrSponge<Other::ScalarField>>(
        &self,
        mut reqs: Vec<UpdateRequest<G, Other>>,
    ) -> Vec<Result<UpdateResponse<G>, &str>>
    {
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

            results[i] = Ok(
                UpdateResponse::<G> {
                    signature: self.signer.sign(self.signing_key, new_acc)
                });
        }

        results
    }
}

impl<G: CommitmentCurve> Params<G> {
    pub fn new(srs : &SRS<G>, endo: G::ScalarField) -> Params<G> {
        Params {
            h: srs.h,
            endo,
            lagrange_commitments: lagrange_commitments(srs)
        }
    }
}
