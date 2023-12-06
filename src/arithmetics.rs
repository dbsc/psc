// #[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct BigInt<const N: usize>{
    num: [u64; N]
}

// impl<const N: usize> Default for BigInt<N> {
//     fn default() -> Self {
//         Self([0u64; N])
//     }
// }

impl<const N: usize> Default for BigInt<N> {
    fn default() -> Self {
        Self{num: [0u64; N]}
    }
}


// /// Sets a = a + b + carry, and returns the new carry.
// #[inline(always)]
// #[allow(unused_mut)]
// #[doc(hidden)]
// pub fn adc(a: &mut u64, b: u64, carry: u64) -> u64 {
//     let tmp = *a as u128 + b as u128 + carry as u128;
//     *a = tmp as u64;
//     (tmp >> 64) as u64
// }

/// Sets a = a + b + carry, and returns the new carry.
pub fn adc_for_add_with_carry(a: &mut u64, b: u64, carry: u8) -> u8 {
    {
        let tmp = *a as u128 + b as u128 + carry as u128;
        *a = tmp as u64;
        (tmp >> 64) as u8
    }
}


/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant limb first.
// TODO: get rid of this trait once we can use associated constants in const generics.
pub trait BigInteger
    // Copy
    // + Clone
    // + Default

{
    // /// Number of 64-bit limbs representing `Self`.
    // const NUM_LIMBS: usize;

    /// Add another [`BigInteger`] to `self`. This method stores the result in `self`,
    /// and returns a carry bit.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut x) = (B::from(1u64), B::from(2u64));
    /// let carry = x.add_with_carry(&one);
    /// assert_eq!(x, B::from(3u64));
    /// assert_eq!(carry, false);
    ///
    /// // Edge-Case
    /// let mut x = B::from(u64::MAX);
    /// let carry = x.add_with_carry(&one);
    /// assert_eq!(x, B::from(0u64));
    /// assert_eq!(carry, true)
    /// ```
    fn add_with_carry(&mut self, other: &Self) -> bool;
}

impl<const N: usize> BigInteger for BigInt<N> {
    // const NUM_LIMBS: usize = N;

    // #[inline]
    fn add_with_carry(&mut self, other: &Self) -> bool {
        {
            use adc_for_add_with_carry as adc;

            let a = &mut self.num;
            let b = &other.num;
            let mut carry = 0;

            if N >= 1 {
                carry = adc(&mut a[0], b[0], carry);
            }
            // if N >= 2 {
            //     carry = adc(&mut a[1], b[1], carry);
            // }
            // if N >= 3 {
            //     carry = adc(&mut a[2], b[2], carry);
            // }
            // if N >= 4 {
            //     carry = adc(&mut a[3], b[3], carry);
            // }
            // if N >= 5 {
            //     carry = adc(&mut a[4], b[4], carry);
            // }
            // if N >= 6 {
            //     carry = adc(&mut a[5], b[5], carry);
            // }
            // for i in 6..N {
            //     carry = adc(&mut a[i], b[i], carry);
            // }
            carry != 0
        }
    }
}