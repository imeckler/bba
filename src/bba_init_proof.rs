use crate::proof_system::*;
use crate::schnorr;

use ark_ec::AffineCurve;
use ark_ff::{FftField, PrimeField};

use schnorr::CoordinateCurve;

// Proof spec:
// Public input:
//  [acc : curve_point]
// Statement:
//  I know
//   [r : scalar],
//   [c : scalar],
//   [alpha : scalar[5]] such that
//   [acc = r * H + c * L_0 + alpha[0] * L_2 + .. + alpha[4] * L_6]

#[derive(Copy, Clone)]
pub struct Params<G> {
    pub lagrange_commitments: [G; 2 + ZK_ROWS],
    pub h: G,
}

#[derive(Copy, Clone)]
pub struct Witness<G: AffineCurve> {
    pub r: G::ScalarField,
    pub c: G::ScalarField,
    pub alpha: [G::ScalarField; ZK_ROWS],
}

pub fn circuit<
    F: PrimeField + FftField,
    G: AffineCurve<BaseField = F> + CoordinateCurve,
    Sys: Cs<F>,
>(
    params: &Params<G>,
    w: &Option<Witness<G>>,
    sys: &mut Sys,
    public_input: Vec<Var<F>>,
) {
    let constant_curve_pt = |sys: &mut Sys, (x, y)| {
        let x = sys.constant(x);
        let y = sys.constant(y);
        (x, y)
    };
    let len = G::ScalarField::size_in_bits();
    let shift: G::ScalarField = shift::<G::ScalarField>(len - 1);
    let rh = {
        let h = constant_curve_pt(sys, params.h.to_coords().unwrap());
        let r = sys.scalar(len, || (w.as_ref().unwrap().r - &shift).into_repr());
        sys.scalar_mul(h, r)
    };
    let cl0 = {
        let l0 = constant_curve_pt(sys, params.lagrange_commitments[0].to_coords().unwrap());
        let c = sys.scalar(len, || (w.as_ref().unwrap().c - &shift).into_repr());
        sys.scalar_mul(l0, c)
    };

    let alpha_point = |sys: &mut Sys, i| {
        let g: G = params.lagrange_commitments[2 + i];
        let g: (F, F) = g.to_coords().unwrap();
        let base = constant_curve_pt(sys, g);
        let alpha_i = sys.scalar(len, || {
            let a: G::ScalarField = w.as_ref().unwrap().alpha[i] - &shift;
            a.into_repr()
        });
        sys.scalar_mul(base, alpha_i)
    };

    let alpha_part = {
        let mut acc = alpha_point(sys, 0);
        for i in 1..5 {
            let alpha_pt = alpha_point(sys, i);
            let new_acc = sys.add_group(acc, alpha_pt);
            acc = new_acc
        }
        acc
    };
    let rh_cl0 = sys.add_group(rh, cl0);
    sys.assert_add_group(rh_cl0, alpha_part, (public_input[0], public_input[1]));
    sys.zk()
}
