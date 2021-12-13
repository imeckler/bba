use ark_ff::PrimeField;

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
pub struct EndoScalar<A: PrimeField>(pub A);

impl<F: PrimeField> EndoScalar<F> {
    pub fn to_field(&self, endo_coeff: &F) -> F {
        let length_in_bits: usize = 256;

        let EndoScalar(x) = self;
        let mut bits = x.into_repr().to_bits();
        bits.reverse();
        assert_eq!(length_in_bits, bits.len());

        let mut a: F = (2 as u64).into();
        let mut b: F = (2 as u64).into();

        let one = F::one();
        let neg_one = -one;

        for i in (0..(length_in_bits / 2)).rev() {
            a.double_in_place();
            b.double_in_place();

            let r_2i = bits[2 * i];
            let s = if !r_2i { &neg_one } else { &one };

            if !bits[2 * i + 1] {
                b += s;
            } else {
                a += s;
            }
        }

        a * endo_coeff + &b
    }
}
