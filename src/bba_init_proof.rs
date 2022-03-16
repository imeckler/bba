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

// TODO: Would be better to replace all these values by endoscalars
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
    constants: &Constants<F>,
    params: &Params<G>,
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
    let len = G::ScalarField::size_in_bits();
    let rh = {
        let h = constant_curve_pt(sys, params.h.to_coords().unwrap());
        let r = sys.scalar(len, || w.as_ref().unwrap().r);
        sys.scalar_mul(zero, h, r)
    };
    let cl0 = {
        let l0 = constant_curve_pt(sys, params.lagrange_commitments[0].to_coords().unwrap());
        let c = sys.scalar(len, || w.as_ref().unwrap().c);
        sys.scalar_mul(zero, l0, c)
    };

    let alpha_point = |sys: &mut Sys, i| {
        let g: G = params.lagrange_commitments[2 + i];
        let g: (F, F) = g.to_coords().unwrap();
        let base = constant_curve_pt(sys, g);
        let alpha_i = sys.scalar(len, || w.as_ref().unwrap().alpha[i]);
        sys.scalar_mul(zero, base, alpha_i)
    };

    let alpha_part = {
        let mut acc = alpha_point(sys, 0);
        for i in 1..ZK_ROWS {
            let alpha_pt = alpha_point(sys, i);
            let new_acc = sys.add_group(zero, acc, alpha_pt);
            acc = new_acc
        }
        acc
    };
    let rh_cl0 = sys.add_group(zero, rh, cl0);
    sys.assert_add_group(zero, rh_cl0, alpha_part, (public_input[0], public_input[1]));
    sys.zk()
}
