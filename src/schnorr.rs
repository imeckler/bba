use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{BigInteger, PrimeField, UniformRand, Zero};
use commitment_dlog::commitment::CommitmentCurve;
use oracle::poseidon::*;
use oracle::sponge::ScalarChallenge;

pub trait CoordinateCurve: AffineCurve {
    fn to_coords(&self) -> Option<(Self::BaseField, Self::BaseField)>;
}

impl<G: CommitmentCurve> CoordinateCurve for G {
    fn to_coords(&self) -> Option<(Self::BaseField, Self::BaseField)> {
        CommitmentCurve::to_coordinates(self)
    }
}

pub type PrivateKey<G> = <G as AffineCurve>::ScalarField;
pub type PublicKey<G> = G;

pub type Signature<G> = (
    <G as AffineCurve>::BaseField,
    <G as AffineCurve>::ScalarField,
);

// TODO: Remove the evenness check. not needed
fn even<F: PrimeField>(x: F) -> bool {
    let bits = x.into_repr().to_bits_le();
    !bits[0]
}

pub trait SignatureParams {
    type BaseField: PrimeField;
    type G: CoordinateCurve<BaseField = Self::BaseField>;
    type Message;

    fn hash(
        &self,
        pk: PublicKey<Self::G>,
        m: Self::Message,
        r: <Self::G as AffineCurve>::BaseField,
    ) -> <Self::G as AffineCurve>::ScalarField;

    fn sign(&self, d: PrivateKey<Self::G>, m: Self::Message) -> Signature<Self::G> {
        let base = Self::G::prime_subgroup_generator();
        let pubkey = base.mul(d).into_affine();
        let (r, k) = {
            let k_prime = <Self::G as AffineCurve>::ScalarField::rand(&mut rand::thread_rng());
            let (r, ry) = base.mul(k_prime).into_affine().to_coords().unwrap();
            let k = if even(ry) { k_prime } else { -k_prime };
            (r, k)
        };

        let e = self.hash(pubkey, m, r);
        let s = k + &(e * &d);
        (r, s)
    }

    fn verify(&self, pk: PublicKey<Self::G>, m: Self::Message, (r, s): Signature<Self::G>) -> bool {
        let e = self.hash(pk, m, r);
        let pt = Self::G::prime_subgroup_generator().mul(s) - &pk.mul(e);
        match pt.into_affine().to_coords() {
            None => false,
            Some((rx, ry)) => even(ry) && rx == r,
        }
    }
}

#[derive(Clone)]
pub struct Signer<G: CoordinateCurve> {
    pub sponge: ArithmeticSpongeParams<G::BaseField>,
    pub endo: G::ScalarField,
}

fn pack<B: BigInteger>(limbs_lsb: &[u64]) -> B {
    let mut res: B = 0.into();
    for &x in limbs_lsb.iter().rev() {
        res.muln(64);
        res.add_nocarry(&x.into());
    }
    res
}

pub const CHALLENGE_LENGTH_IN_BITS: usize = 256;

impl<G: CoordinateCurve> SignatureParams for Signer<G>
where
    G::BaseField: PrimeField,
{
    type BaseField = G::BaseField;
    type G = G;
    type Message = G;

    // TODO
    fn hash(&self, _pk: PublicKey<G>, m: G, r: G::BaseField) -> G::ScalarField {
        let (x, y) = m.to_coords().unwrap();

        let mut s = vec![x, y, r];
        oracle::poseidon::poseidon_block_cipher::<G::BaseField, PlonkSpongeConstants15W>(
            &self.sponge,
            &mut s,
        );
        ScalarChallenge(G::ScalarField::from_repr(pack(s[0].into_repr().as_ref())).unwrap())
            .to_field_with_length(CHALLENGE_LENGTH_IN_BITS, &self.endo)
    }
}
