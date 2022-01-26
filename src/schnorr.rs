use ark_ff::{BigInteger, PrimeField, UniformRand, Zero};
use ark_ec::{AffineCurve, ProjectiveCurve};
use array_init::array_init;
use commitment_dlog::commitment::CommitmentCurve;
use oracle::poseidon::*;
use oracle::sponge::ScalarChallenge;

use crate::random_oracle;

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

const COLUMNS: usize = 5;

fn pack<B: BigInteger>(limbs_lsb: &[u64]) -> B {
    let mut res: B = 0.into();
    for &x in limbs_lsb.iter().rev() {
        res.muln(64);
        res.add_nocarry(&x.into());
    }
    res
}

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
        let input = [x, y, r, G::BaseField::zero(), G::BaseField::zero()];
        let res = (0..random_oracle::POSEIDON_ROUNDS).fold(input, |prev, round| {
            let rc = &self.sponge.round_constants[round];
            let s: [_; COLUMNS] = array_init(|j| sbox::<_, PlonkSpongeConstants15W>(prev[j]));
            array_init(|i| {
                let m = &self.sponge.mds[i];
                rc[i]
                    + &s.iter()
                        .zip(m.iter())
                        .fold(G::BaseField::zero(), |x, (s, &m)| m * s + x)
            })
        });

        ScalarChallenge(G::ScalarField::from_repr(pack(res[0].into_repr().as_ref())).unwrap())
            .to_field(&self.endo)
    }
}
