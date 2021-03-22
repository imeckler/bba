use crate::proof_system::*;
use crate::schnorr;
use algebra::{AffineCurve, FftField, PrimeField};
use schnorr::CoordinateCurve;

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
    pub r: G::ScalarField,
}

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
    let constant_curve_pt = |sys: &mut Sys, (x, y)| {
        let x = sys.constant(x);
        let y = sys.constant(y);
        (x, y)
    };
    let mask = {
        let h = constant_curve_pt(sys, params.h);
        let r = sys.scalar(256, || w.as_ref().unwrap().r.into_repr());
        sys.endo(constants, h, r)
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
            let input = [prev_acc.0, prev_acc.1, r, zero, zero];
            let e = sys.poseidon(constants, input)[0];
            let e_bits = sys.scalar(256, || e.val().into_repr());
            sys.assert_pack(e, &e_bits);
            e_bits
        };
        let neg_e_pk = {
            let (x, y) = sys.endo(constants, pubkey, e);
            // optimization: Could save a constraint by not explicitly doing the negation and using
            // sys.assert_add_group
            (x, sys.scale(-F::one(), y))
        };
        let (rx, ry) = {
            let base = constant_curve_pt(sys, constants.base);
            let len = G::ScalarField::size_in_bits();
            let s = sys.scalar(len, || {
                (w.as_ref().unwrap().signature.1 - &shift::<G::ScalarField>(len - 1)).into_repr()
            });
            // TODO: Need to check that s is not one of the two forbidden values
            let s_g = sys.scalar_mul(base, s);
            sys.add_group(s_g, neg_e_pk)
        };
        // optimization: Could save a constraint in constraining y to be even
        let ry_bits = {
            let bs = sys.scalar(256, || ry.val().into_repr());
            sys.assert_pack(ry, &bs);
            bs
        };
        sys.assert_eq(zero, ry_bits[0]);
        sys.assert_eq(rx, r);
    }
    sys.assert_add_group(mask, prev_acc, (public_input[0], public_input[1]));
    sys.zk()
}
