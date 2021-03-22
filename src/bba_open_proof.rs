use crate::bba;
use crate::proof_system::*;
use crate::schnorr;
use algebra::{AffineCurve, FftField, PrimeField};
use array_init::array_init;
use plonk_5_wires_circuits::gate::GateType;
use schnorr::CoordinateCurve;

// c, total value
pub const PUBLIC_INPUT: usize = 2;

// Parameters for the update proof circuit.
#[derive(Clone)]
pub struct Params {
    pub prices: Vec<u32>,
}

pub struct Witness {
    pub counters: Vec<u32>,
}

pub fn circuit<
    F: PrimeField + FftField,
    G: AffineCurve<BaseField = F> + CoordinateCurve,
    Sys: Cs<F>,
>(
    params: &Params,
    w: &Option<Witness>,
    sys: &mut Sys,
    public_input: Vec<Var<F>>,
) {
    let counter = |i| F::from(w.as_ref().unwrap().counters[i] as u64);
    let price = |i| F::from(params.prices[i] as u64);
    let mut acc = sys.var(|| counter(0) * price(0));
    let row0 = [
        sys.var(|| counter(0)),
        acc,
        sys.var(|| F::zero()),
        sys.var(|| F::zero()),
        sys.var(|| F::zero()),
    ];
    sys.gate(GateSpec {
        typ: GateType::Generic,
        row: row0,
        c: vec![
            price(0),
            -F::one(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
        ],
    });

    for i in 1..bba::MAX_COUNTERS {
        let new_acc = if i == bba::MAX_COUNTERS - 1 {
            public_input[1]
        } else {
            sys.var(|| acc.val() + counter(i) * price(i))
        };
        let row = [
            sys.var(|| counter(i)),
            acc,
            new_acc,
            sys.var(|| F::zero()),
            sys.var(|| F::zero()),
        ];
        sys.gate(GateSpec {
            typ: GateType::Generic,
            row: row,
            c: vec![
                price(i),
                F::one(),
                -F::one(),
                F::zero(),
                F::zero(),
                F::zero(),
                F::zero(),
            ],
        });
        acc = new_acc;
    }

    for _ in 0..ZK_ROWS {
        let row = array_init(|i| {
            if i == 0 {
                sys.var(|| F::zero())
            } else {
                sys.var(|| F::rand(&mut rand_core::OsRng))
            }
        });
        // constrain first column to 0
        sys.gate(GateSpec {
            typ: GateType::Generic,
            c: vec![
                F::one(),
                F::zero(),
                F::zero(),
                F::zero(),
                F::zero(),
                F::zero(),
                F::zero(),
            ],
            row,
        });
    }
}
