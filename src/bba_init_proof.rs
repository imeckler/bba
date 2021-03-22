use crate::proof_system::*;
use crate::schnorr;
use algebra::{AffineCurve, FftField, PrimeField};
use schnorr::CoordinateCurve;

// Proof spec:
// Public input:
//  [acc : curve_point]
// Statement:
//  I know [r : scalar], [c : scalar] such that [acc = r * H + c * L_0]

#[derive(Copy, Clone)]
pub struct Params<F> {
    pub l0: (F, F),
    pub h: (F, F),
}

#[derive(Copy, Clone)]
pub struct Witness<G: AffineCurve> {
    pub r: G::ScalarField,
    pub c: G::ScalarField,
}

pub fn circuit<
    F: PrimeField + FftField,
    G: AffineCurve<BaseField = F> + CoordinateCurve,
    Sys: Cs<F>,
>(
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
    let len = G::ScalarField::size_in_bits();
    let shift = shift::<G::ScalarField>(len - 1);
    let rh = {
        let h = constant_curve_pt(sys, params.h);
        let r = sys.scalar(len, || (w.as_ref().unwrap().r - &shift).into_repr());
        sys.scalar_mul(h, r)
    };
    let cl0 = {
        let l0 = constant_curve_pt(sys, params.l0);
        let c = sys.scalar(len, || (w.as_ref().unwrap().c - &shift).into_repr());
        sys.scalar_mul(l0, c)
    };
    sys.assert_add_group(rh, cl0, (public_input[0], public_input[1]));
    sys.zk()
}
