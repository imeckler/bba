use crate::random_oracle;
use algebra::{
    pasta::{fp::Fp, fq::Fq, pallas::Affine as Other, vesta::Affine},
    AffineCurve, BigInteger, FftField, Field, One, PrimeField, ProjectiveCurve, SquareRootField,
    Zero,
};
use array_init::array_init;
use commitment_dlog::{
    commitment::{ceil_log2, CommitmentCurve, PolyComm},
    srs::{endos, SRS},
};
use oracle::{poseidon::ArithmeticSpongeParams, poseidon::*, FqSponge};
use plonk_circuits::{
    constraints::ConstraintSystem,
    gate::{CircuitGate, GateType},
    wires::Wire,
};
use plonk_protocol_dlog::{
    index::{Index, SRSSpec}, 
    plonk_sponge::FrSponge, 
    prover::ProverProof
};
use std::collections::HashMap;

pub const COLUMNS: usize = 5;
pub const ZK_ROWS: usize = 5;

pub trait Cycle {
    type InnerField: FftField
        + PrimeField
        + SquareRootField
        + From<u128>
        + From<u64>
        + From<u32>
        + From<u16>
        + From<u8>;
    type OuterField: FftField
        + PrimeField
        + SquareRootField
        + From<u128>
        + From<u64>
        + From<u32>
        + From<u16>
        + From<u8>;

    type InnerMap: groupmap::GroupMap<Self::InnerField>;
    type OuterMap: groupmap::GroupMap<Self::OuterField>;

    type InnerProj: ProjectiveCurve<
            Affine = Self::Inner,
            ScalarField = Self::OuterField,
            BaseField = Self::InnerField,
        > + From<Self::Inner>
        + Into<Self::Inner>
        + std::ops::MulAssign<Self::OuterField>;

    type Inner: CommitmentCurve<
            Projective = Self::InnerProj,
            Map = Self::InnerMap,
            BaseField = Self::InnerField,
            ScalarField = Self::OuterField,
        > + From<Self::InnerProj>
        + Into<Self::InnerProj>;

    type OuterProj: ProjectiveCurve<
            Affine = Self::Outer,
            ScalarField = Self::InnerField,
            BaseField = Self::OuterField,
        > + From<Self::Outer>
        + Into<Self::Outer>
        + std::ops::MulAssign<Self::InnerField>;

    type Outer: CommitmentCurve<
        Projective = Self::OuterProj,
        Map = Self::OuterMap,
        ScalarField = Self::InnerField,
        BaseField = Self::OuterField,
    >;
}

pub struct FpInner;
pub struct FqInner;

impl Cycle for FpInner {
    type InnerMap = <Other as CommitmentCurve>::Map;
    type OuterMap = <Affine as CommitmentCurve>::Map;

    type InnerField = Fp;
    type OuterField = Fq;
    type Inner = Other;
    type Outer = Affine;
    type InnerProj = <Other as AffineCurve>::Projective;
    type OuterProj = <Affine as AffineCurve>::Projective;
}

impl Cycle for FqInner {
    type InnerMap = <Affine as CommitmentCurve>::Map;
    type OuterMap = <Other as CommitmentCurve>::Map;

    type InnerField = Fq;
    type OuterField = Fp;
    type Inner = Affine;
    type Outer = Other;
    type InnerProj = <Affine as AffineCurve>::Projective;
    type OuterProj = <Other as AffineCurve>::Projective;
}

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
pub struct Var<F> {
    pub index: usize,
    pub value: Option<F>,
}

impl<F: Copy> Var<F> {
    pub fn val(&self) -> F {
        self.value.unwrap()
    }
}

pub struct GateSpec<F: FftField> {
    pub typ: GateType,
    pub row: [Var<F>; COLUMNS],
    pub c: Vec<F>,
}

#[derive(Clone)]
pub struct Constants<F: Field> {
    pub poseidon: ArithmeticSpongeParams<F>,
    pub endo: F,
    pub base: (F, F),
}

pub struct System<F: FftField> {
    pub next_variable: usize,
    // pub equivalence_classes: HashMap<Var, Vec<Position>>,
    pub gates: Vec<GateSpec<F>>,
}

pub struct WitnessGenerator<F> {
    pub rows: Vec<Row<F>>,
}

type Row<V> = [V; COLUMNS];

pub trait Cs<F: FftField> {
    fn var<G>(&mut self, g: G) -> Var<F>
    where
        G: FnOnce() -> F;

    fn scalar<G, N: BigInteger>(&mut self, length: usize, g: G) -> Vec<Var<F>>
    where
        G: FnOnce() -> N,
    {
        let mut s = None;
        let mut res = vec![];

        res.push(self.var(|| {
            let mut v = g().to_bits();
            v.reverse();
            let res = bool_to_field(v[0]);
            s = Some(v);
            res
        }));

        for i in 1..length {
            res.push(self.var(|| match &s {
                Some(v) => bool_to_field(v[i]),
                None => panic!(),
            }))
        }
        res
    }

    fn gate(&mut self, g: GateSpec<F>);

    // TODO: Optimize to use permutation argument.
    fn assert_eq(&mut self, x1: Var<F>, x2: Var<F>) {
        let row = array_init(|i| {
            if i == 0 {
                x1
            } else if i == 1 {
                x2
            } else {
                self.var(|| F::zero())
            }
        });

        let mut c = vec![F::zero(); COLUMNS + 2];
        c[0] = F::one();
        c[1] = -F::one();

        self.gate(GateSpec {
            typ: GateType::Generic,
            row,
            c,
        });
    }

    fn constant(&mut self, x: F) -> Var<F> {
        let v = self.var(|| x);

        let mut c = vec![F::zero(); COLUMNS + 2];
        c[0] = F::one();
        c[COLUMNS + 1] = -x;

        let row = array_init(|i| {
            if i == 0 {
                v.clone()
            } else {
                self.var(|| F::zero())
            }
        });

        self.gate(GateSpec {
            typ: GateType::Generic,
            row,
            c,
        });
        v
    }

    fn scale(&mut self, x: F, v: Var<F>) -> Var<F> {
        let xv = self.var(|| v.val() * x);
        let row = [
            v,
            xv,
            self.var(|| F::zero()),
            self.var(|| F::zero()),
            self.var(|| F::zero()),
        ];
        let mut c = vec![F::zero(); COLUMNS + 2];
        c[0] = x;
        c[1] = -F::one();
        self.gate(GateSpec {
            typ: GateType::Generic,
            row,
            c,
        });
        xv
    }

    fn double(&mut self, (x1, y1): (Var<F>, Var<F>)) -> (Var<F>, Var<F>) {
        let y1_inv = self.var(|| y1.val().inverse().unwrap());

        let mut r = None;
        let x2 = self.var(|| {
            let p = (x1.val(), y1.val());
            let pp = add_points(p, p);
            r = Some(pp);
            pp.0
        });
        let y2 = self.var(|| r.unwrap().1);
        drop(r);

        self.gate(GateSpec {
            typ: GateType::Double,
            row: [x1, y1, x2, y2, y1_inv],
            c: vec![],
        });
        (x2, y2)
    }

    fn assert_add_group(&mut self, (x1, y1): (Var<F>, Var<F>), (x2, y2): (Var<F>, Var<F>), (x3, y3): (Var<F>, Var<F>)) {
        let inv = self.var(|| (x2.val() - x1.val()).inverse().unwrap());
        self.gate(GateSpec {
            typ: GateType::Add,
            row: [x1, y1, x2, y2, inv],
            c: vec![],
        });
        let row2 = [
            x3,
            y3,
            self.var(|| F::zero()),
            self.var(|| F::zero()),
            self.var(|| F::zero()),
        ];
        self.gate(GateSpec {
            typ: GateType::Zero,
            row: row2,
            c: vec![],
        });
    }

    fn add_group(&mut self, (x1, y1): (Var<F>, Var<F>), (x2, y2): (Var<F>, Var<F>)) -> (Var<F>, Var<F>) {
        let mut r = None;
        let x3 = self.var(|| {
            let pq = add_points((x1.val(), y1.val()), (x2.val(), y2.val()));
            r = Some(pq);
            pq.0
        });
        let y3 = self.var(|| r.unwrap().1);

        drop(r);

        self.assert_add_group((x1, y1), (x2, y2), (x3, y3));

        (x3, y3)
    }

    fn cond_select(&mut self, b: Var<F>, t: Var<F>, f: Var<F>) -> Var<F> {
        // Could maybe be more efficient
        // delta = t - f
        // res = f + b * delta

        let delta = self.var(|| t.val() - f.val());
        let res = self.var(|| f.val() + b.val() * delta.val());

        let row1 = [t, f, delta, self.var(|| F::zero()), self.var(|| F::zero())];
        let mut c1 = vec![F::zero(); COLUMNS + 2];
        c1[0] = F::one();
        c1[1] = -F::one();
        c1[2] = -F::one();
        self.gate(GateSpec {
            typ: GateType::Generic,
            row: row1,
            c: c1,
        });

        let row2 = [b, delta, f, res, self.var(|| F::zero())];
        let one = F::one();
        let z = F::zero();
        let c2 = vec![z, z, one, -one, z, one, z];
        self.gate(GateSpec {
            typ: GateType::Generic,
            row: row2,
            c: c2,
        });
        res
    }

    fn scalar_mul(&mut self, (xt, yt): (Var<F>, Var<F>), bits: Vec<Var<F>>) -> (Var<F>, Var<F>) {
        let (mut xp, mut yp) = self.double((xt, yt));
        // xt yt s1 s2 b
        // xs ys xp yp _
        for i in (0..bits.len() - 1).rev() {
            let b = bits[i + 1];
            let yq = self.var(|| {
                if b.val().is_zero() {
                    -yt.val()
                } else {
                    yt.val()
                }
            });

            let (xs, ys) = {
                let mut s = None;
                let xs = self.var(|| {
                    let p = (xp.val(), yp.val());
                    let s_pt = add_points(add_points((xt.val(), yq.val()), p), p);
                    s = Some(s_pt);
                    s_pt.0
                });
                let ys = self.var(|| s.unwrap().1);
                (xs, ys)
            };

            let s1 = self.var(|| (yq.val() - &yp.val()) / &(xt.val() - &xp.val()));
            let s2 = self.var(|| (ys.val() + &yp.val()) / &(xp.val() - &xs.val()));

            self.gate(GateSpec {
                typ: GateType::Vbmul1,
                row: [xt, yt, s1, s2, b],
                c: vec![],
            });
            let z = self.var(|| F::zero());
            self.gate(GateSpec {
                typ: GateType::Zero,
                row: [xs, ys, xp, yp, z],
                c: vec![],
            });

            xp = xs;
            yp = ys;
        }

        let neg_t = (xt, self.scale(-F::one(), yt));
        let (xr, yr) = self.add_group((xp, yp), neg_t);

        let mut bool0_row = [self.var(|| F::zero()); COLUMNS];
        bool0_row[0] = bits[0];
        bool0_row[1] = bits[0];
        self.gate(GateSpec {
            typ: GateType::Generic,
            row: bool0_row,
            c: vec![
                F::one(),
                F::zero(),
                F::zero(),
                F::zero(),
                F::zero(),
                -F::one(),
                F::zero(),
            ],
        });
        (
            self.cond_select(bits[0], xp, xr),
            self.cond_select(bits[0], yp, yr),
        )
    }

    fn endo(
        &mut self,
        constants: &Constants<F>,
        (xt, yt): (Var<F>, Var<F>),
        bits: Vec<Var<F>>,
    ) -> (Var<F>, Var<F>) {
        let endo = constants.endo;

        // 2(phi(p) + p)
        let (mut xp, mut yp) = {
            let phip = (self.scale(endo, xt), yt);
            let phip_p = self.add_group(phip, (xt, yt));
            self.double(phip_p)
        };

        for i in (0..128).rev() {
            let b_2i = bits[2 * i];
            let b_2i1 = bits[2 * i + 1];
            let xq = self.var(|| (F::one() + (endo - F::one()) * b_2i1.val()) * xt.val());
            let yq = self.var(|| (b_2i.val().double() - F::one()) * yt.val());

            let mut p = None;
            let xs = self.var(|| {
                let r = add_points(
                    add_points((xq.val(), yq.val()), (xp.val(), yp.val())),
                    (xp.val(), yp.val()),
                );
                p = Some(r);
                r.0
            });
            let ys = self.var(|| p.unwrap().1);
            drop(p);

            let s1 = self.var(|| (yq.val() - &yp.val()) / &(xq.val() - &xp.val()));
            let s2 = self.var(|| (ys.val() + &yp.val()) / &(xp.val() - &xs.val()));
            self.gate(GateSpec {
                typ: GateType::Endomul,
                row: [xt, yt, s1, s2, b_2i],
                c: vec![],
            });
            self.gate(GateSpec {
                typ: GateType::Zero,
                row: [xs, ys, xp, yp, b_2i1],
                c: vec![],
            });

            xp = xs;
            yp = ys;
        }
        (xp, yp)
    }

    fn assert_pack(&mut self, x: Var<F>, bits_lsb: &Vec<Var<F>>) {
        let z = self.constant(F::zero());
        let init = [z, z, z, z, z];
        self.gate(GateSpec {
            typ: GateType::Pack,
            row: init,
            c: vec![],
        });

        assert_eq!(bits_lsb.len(), 256);
        let mut bits_msb = bits_lsb.clone();
        bits_msb.reverse();
        let mut acc = z;
        for k in 0..63 {
            let new_acc = self.var(|| {
                bits_msb[4 * k + 3].val()
                    + &bits_msb[4 * k + 2].val().double()
                    + &bits_msb[4 * k + 1].val().double().double()
                    + &bits_msb[4 * k].val().double().double().double()
                    + &acc.val().double().double().double().double()
            });
            self.gate(GateSpec {
                typ: GateType::Pack,
                c: vec![],
                row: [
                    bits_msb[4 * k],
                    bits_msb[4 * k + 1],
                    bits_msb[4 * k + 2],
                    bits_msb[4 * k + 3],
                    new_acc,
                ],
            });
            acc = new_acc;
        }
        let k = 63;
        self.gate(GateSpec {
            typ: GateType::Zero,
            c: vec![],
            row: [
                bits_msb[4 * k],
                bits_msb[4 * k + 1],
                bits_msb[4 * k + 2],
                bits_msb[4 * k + 3],
                x,
            ],
        });
    }

    fn zk(&mut self) {
        for _ in 0..ZK_ROWS {
            let row = array_init(|_| self.var(|| F::rand(&mut rand_core::OsRng)));
            self.gate(GateSpec {
                typ: GateType::Zero,
                c: vec![],
                row,
            });
        }
    }

    fn poseidon(&mut self, constants: &Constants<F>, input: Row<Var<F>>) -> Row<Var<F>> {
        let params = &constants.poseidon;
        let res = (0..random_oracle::POSEIDON_ROUNDS).fold(input.clone(), |prev, round| {
            let rc = constants.poseidon.round_constants[round].clone();

            let next: [Var<F>; COLUMNS] = array_init(|i| {
                let m = params.mds[i].clone();
                self.var(|| {
                    // TODO: Lift out
                    let this: [F; COLUMNS] =
                        array_init(|j| sbox::<F, PlonkSpongeConstants5W>(prev[j].value.unwrap()));
                    rc[i]
                        + &this
                            .iter()
                            .zip(m.iter())
                            .fold(F::zero(), |x, (s, &m)| m * s + x)
                })
            });

            self.gate(GateSpec {
                typ: GateType::Poseidon,
                c: rc,
                row: prev,
            });

            next
        });
        let z = F::zero();
        self.gate(GateSpec {
            typ: GateType::Generic,
            c: vec![z, z, z, z, z, z, z],
            row: res,
        });
        res
    }
}

fn add_points<F: Field>(a: (F, F), b: (F, F)) -> (F, F) {
    if a == (F::zero(), F::zero()) {
        b
    } else if b == (F::zero(), F::zero()) {
        a
    } else if a.0 == b.0 && (a.1 != b.1 || b.1 == F::zero()) {
        (F::zero(), F::zero())
    } else if a.0 == b.0 && a.1 == b.1 {
        let sq = a.0.square();
        let s = (sq.double() + &sq) / &a.1.double();
        let x = s.square() - &a.0.double();
        let y = -a.1 - &(s * &(x - &a.0));
        (x, y)
    } else {
        let s = (a.1 - &b.1) / &(a.0 - &b.0);
        let x = s.square() - &a.0 - &b.0;
        let y = -a.1 - &(s * &(x - &a.0));
        (x, y)
    }
}

fn bool_to_field<F: Field>(b: bool) -> F {
    if b {
        F::one()
    } else {
        F::zero()
    }
}

impl<F: FftField> Cs<F> for WitnessGenerator<F> {
    fn var<G>(&mut self, g: G) -> Var<F>
    where
        G: FnOnce() -> F,
    {
        Var {
            index: 0,
            value: Some(g()),
        }
    }

    fn gate(&mut self, g: GateSpec<F>) {
        self.rows.push(array_init(|i| g.row[i].value.unwrap()))
    }
}

impl<F: FftField> WitnessGenerator<F> {
    fn columns(&self) -> [Vec<F>; COLUMNS] {
        array_init(|col| {
            let mut v: Vec<_> = self.rows.iter().map(|row| row[col]).collect();
            for _ in 0..((1 << ceil_log2(v.len())) - v.len()) {
                v.push(F::zero())
            }
            v
        })
    }
}

impl<F: FftField> Cs<F> for System<F> {
    fn var<G>(&mut self, _: G) -> Var<F> {
        let v = self.next_variable;
        self.next_variable += 1;
        Var {
            index: v,
            value: None,
        }
    }

    fn gate(&mut self, g: GateSpec<F>) {
        self.gates.push(g);
    }
}

impl<F: FftField> System<F> {
    pub fn gates(&self) -> Vec<CircuitGate<F>> {
        let mut first_cell: HashMap<usize, Wire> = HashMap::new();
        let mut most_recent_cell: HashMap<usize, Wire> = HashMap::new();
        let mut gates = vec![];

        for (i, gs) in self.gates.iter().enumerate() {
            let wires = array_init(|j| -> Wire {
                let v = gs.row[j].index;
                let curr = Wire { row: i, col: j };
                match most_recent_cell.insert(v, curr) {
                    Some(w) => w,
                    None => {
                        first_cell.insert(v, curr);
                        curr
                    }
                }
            });
            let g = CircuitGate {
                row: i,
                typ: gs.typ.clone(),
                c: gs.c.clone(),
                wires,
            };
            gates.push(g);
        }

        for (v, first) in first_cell.iter() {
            let last = most_recent_cell.get(v).unwrap().clone();
            gates[first.row].wires[first.col] = last;
        }

        return gates;
    }
}

pub fn prove<
    'a,
    G: CommitmentCurve,
    H,
    EFqSponge: Clone + FqSponge<G::BaseField, G, G::ScalarField>,
    EFrSponge: FrSponge<G::ScalarField>,
>(
    index: &Index<'a, G>,
    group_map: &G::Map,
    blinders: Option<[Option<G::ScalarField>; COLUMNS]>,
    public_input: Vec<G::ScalarField>,
    main: H,
) -> ProverProof<G>
where
    H: FnOnce(&mut WitnessGenerator<G::ScalarField>, Vec<Var<G::ScalarField>>) -> (),
{
    let mut gen: WitnessGenerator<G::ScalarField> = WitnessGenerator {
        rows: public_input
            .iter()
            .map(|x| array_init(|i| if i == 0 { *x } else { G::ScalarField::zero() }))
            .collect(),
    };

    main(
        &mut gen,
        public_input
            .iter()
            .map(|x| Var {
                index: 0,
                value: Some(*x),
            })
            .collect(),
    );

    let columns = gen.columns();

    let blinders: [Option<PolyComm<G::ScalarField>>; COLUMNS] = match blinders {
        None => array_init(|_| None),
        Some(bs) => array_init(|i| {
            bs[i].map(|b| PolyComm {
                unshifted: vec![b],
                shifted: None,
            })
        }),
    };

    ProverProof::create::<EFqSponge, EFrSponge>(group_map, &columns, index, vec![], blinders)
        .unwrap()
}

pub fn generate_proving_key<'a, C: Cycle, H>(
    srs: &'a SRS<C::Outer>,
    constants: &Constants<C::InnerField>,
    poseidon_params: &ArithmeticSpongeParams<C::OuterField>,
    public: usize,
    main: H,
) -> Index<'a, C::Outer>
where
    H: FnOnce(&mut System<C::InnerField>, Vec<Var<C::InnerField>>) -> (),
{
    let mut system: System<C::InnerField> = System {
        next_variable: 0,
        gates: vec![],
    };
    let z = C::InnerField::zero();
    let public_input_row = vec![C::InnerField::one(), z, z, z, z, z, z];

    let public_input: Vec<_> = (0..public)
        .map(|_| {
            let v = system.var(|| panic!("fail"));
            let row = array_init(|i| {
                if i == 0 {
                    v.clone()
                } else {
                    system.var(|| panic!("fail"))
                }
            });
            system.gate(GateSpec {
                typ: GateType::Generic,
                c: public_input_row.clone(),
                row,
            });
            v
        })
        .collect();

    main(&mut system, public_input);

    let gates = system.gates();
    // Other base field = self scalar field
    let (endo_q, _endo_r) = endos::<C::Inner>();
    Index::<C::Outer>::create(
        ConstraintSystem::<C::InnerField>::create(gates, constants.poseidon.clone(), public)
            .unwrap(),
        poseidon_params.clone(),
        endo_q,
        SRSSpec::Use(&srs),
    )
}

pub fn fp_constants() -> Constants<Fp> {
    let (endo_q, _endo_r) = endos::<Other>();
    let base = Other::prime_subgroup_generator().to_coordinates().unwrap();
    Constants {
        poseidon: oracle::pasta::fp5::params(),
        endo: endo_q,
        base,
    }
}

pub fn fq_constants() -> Constants<Fq> {
    let (endo_q, _endo_r) = endos::<Affine>();
    let base = Affine::prime_subgroup_generator().to_coordinates().unwrap();
    Constants {
        poseidon: oracle::pasta::fq5::params(),
        endo: endo_q,
        base,
    }
}

pub fn shift<F: PrimeField>(size: usize) -> F {
    let two: F = (2 as u64).into();
    two.pow(&[size as u64])
}
