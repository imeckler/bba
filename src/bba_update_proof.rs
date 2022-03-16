use crate::proof_system::*;
use crate::schnorr;
use ark_ec::AffineCurve;
use ark_ff::{FftField, PrimeField};
use oracle::sponge::ScalarChallenge;
use schnorr::{CoordinateCurve, CHALLENGE_LENGTH_IN_BITS};

// Parameters for the update proof circuit.
#[derive(Copy, Clone)]
pub struct Params<F> {
    pub brave_pubkey: (F, F),
    pub h: (F, F),
}

#[derive(Copy, Clone)]
pub struct Witness<G: AffineCurve> {
    pub signature: schnorr::Signature<G>,
    pub acc: G,
    pub r: ScalarChallenge<G::ScalarField>,
}

pub const R_LENGTH_IN_BITS: usize = 256;

// Public input:
//  [new_acc: curve_point]
// Prove:
// I know [acc: curve_point] and [s : signature] such that
// the signature verifies against Brave's public key and [new_acc] is
// a re-randomization of [acc]
pub fn circuit<
    F: PrimeField + FftField,
    G: AffineCurve<BaseField = F> + CoordinateCurve,
    Sys: Cs<F>,
>(
    constants: &Constants<F>,
    params: &Params<F>,
    w: &Option<Witness<G>>,
    sys: &mut Sys,
    public_input: Vec<Var<F>>,
) {
    let zero = sys.constant(F::zero());

    let constant_curve_pt = |sys: &mut Sys, (x, y)| {
        let x = sys.constant(x);
        let y = sys.constant(y);
        (x, y)
    };
    let mask = {
        let h = constant_curve_pt(sys, params.h);
        let r = sys.endo_scalar(R_LENGTH_IN_BITS, || w.as_ref().unwrap().r.0.into_repr());
        sys.endo(zero, constants, h, r, R_LENGTH_IN_BITS)
    };
    let prev_acc = {
        let mut a = None;
        let x = sys.var(|| {
            let cs = w.as_ref().unwrap().acc.to_coords().unwrap();
            a = Some(cs);
            cs.0
        });
        let y = sys.var(|| a.unwrap().1);
        (x, y)
    };
    {
        // Signature verification
        let pubkey = constant_curve_pt(sys, params.brave_pubkey);
        let zero = sys.constant(F::zero());
        let r = sys.var(|| w.as_ref().unwrap().signature.0);
        let e = {
            let input = vec![prev_acc.0, prev_acc.1, r];
            let e = sys.poseidon(constants, input)[0];
            e
        };
        let neg_e_pk = {
            let (x, y) = sys.endo(zero, constants, pubkey, e, CHALLENGE_LENGTH_IN_BITS);
            // optimization: Could save a constraint by not explicitly doing the negation and using
            // sys.assert_add_group
            (x, sys.scale(-F::one(), y))
        };
        let (rx, _ry) = {
            let base = constant_curve_pt(sys, constants.base);
            let len = G::ScalarField::size_in_bits();
            let s = sys.scalar(len, || w.as_ref().unwrap().signature.1);
            // TODO: Need to check that s is not one of the two forbidden values
            let s_g = sys.scalar_mul(zero, base, s);
            sys.add_group(zero, s_g, neg_e_pk)
        };
        sys.assert_eq(rx, r);
    }
    sys.assert_add_group(zero, mask, prev_acc, (public_input[0], public_input[1]));
    sys.zk()
}
