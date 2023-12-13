/// Reference
/// arkworks/algebra ff/src/biginteger/mod.rs

use crate::arithmetic;

pub struct BigInt<const N: usize>(pub [u64; N]);

impl<const N: usize> Default for BigInt<N> {
    fn default() -> Self {
        Self([0u64; N])
    }
}

impl<const N: usize> BigInt<N> {
    pub const fn new(value: [u64; N]) -> Self {
        Self(value)
    }

    pub const fn zero() -> Self {
        Self([0u64; N])
    }

    pub const fn one() -> Self {
        let mut one = Self::zero();
        one.0[0] = 1;
        one
    }

    pub const fn const_is_even(&self) -> bool {
        self.0[0] % 2 == 0
    }

    pub const fn const_is_odd(&self) -> bool {
        self.0[0] % 2 == 1
    }

    pub const fn mod_4(&self) -> u8 {
        (((self.0[0] << 62) >> 62) % 4) as u8
    }

    // pub const fn const_shr(&self) -> Self {
    //     let mut result = *self;
    //     let mut t = 0;
    //     crate::const_for!((i in 0..N) {
    //         let a = result.0[N - i - 1];
    //         let t2 = a << 63;
    //         result.0[N - i - 1] >>= 1;
    //         result.0[N - i - 1] |= t;
    //         t = t2;
    //     });
    //     result
    // }

    // const fn const_geq(&self, other: &Self) -> bool {
    //     const_for!((i in 0..N) {
    //         let a = self.0[N - i - 1];
    //         let b = other.0[N - i - 1];
    //         if a < b {
    //             return false;
    //         } else if a > b {
    //             return true;
    //         }
    //     });
    //     true
    // }

    // pub const fn two_adic_valuation(mut self) -> u32 {
    //     let mut two_adicity = 0;
    //     assert!(self.const_is_odd());
    //     // Since `self` is odd, we can always subtract one
    //     // without a borrow
    //     self.0[0] -= 1;
    //     while self.const_is_even() {
    //         self = self.const_shr();
    //         two_adicity += 1;
    //     }
    //     two_adicity
    // }

    // pub const fn two_adic_coefficient(mut self) -> Self {
    //     assert!(self.const_is_odd());
    //     // Since `self` is odd, we can always subtract one
    //     // without a borrow
    //     self.0[0] -= 1;
    //     while self.const_is_even() {
    //         self = self.const_shr();
    //     }
    //     assert!(self.const_is_odd());
    //     self
    // }

    // pub const fn divide_by_2_round_down(mut self) -> Self {
    //     if self.const_is_odd() {
    //         self.0[0] -= 1;
    //     }
    //     self.const_shr()
    // }

    pub const fn const_num_bits(self) -> u32 {
        ((N - 1) * 64) as u32 + (64 - self.0[N - 1].leading_zeros())
    }

    // pub(crate) const fn const_sub_with_borrow(mut self, other: &Self) -> (Self, bool) {
    //     let mut borrow = 0;

    //     const_for!((i in 0..N) {
    //         self.0[i] = sbb!(self.0[i], other.0[i], &mut borrow);
    //     });

    //     (self, borrow != 0)
    // }

    // pub(crate) const fn const_add_with_carry(mut self, other: &Self) -> (Self, bool) {
    //     let mut carry = 0;

    //     crate::const_for!((i in 0..N) {
    //         self.0[i] = adc!(self.0[i], other.0[i], &mut carry);
    //     });

    //     (self, carry != 0)
    // }

    // const fn const_mul2_with_carry(mut self) -> (Self, bool) {
    //     let mut last = 0;
    //     crate::const_for!((i in 0..N) {
    //         let a = self.0[i];
    //         let tmp = a >> 63;
    //         self.0[i] <<= 1;
    //         self.0[i] |= last;
    //         last = tmp;
    //     });
    //     (self, last != 0)
    // }

    // pub(crate) const fn const_is_zero(&self) -> bool {
    //     let mut is_zero = true;
    //     crate::const_for!((i in 0..N) {
    //         is_zero &= self.0[i] == 0;
    //     });
    //     is_zero
    // }

    // pub const fn montgomery_r(&self) -> Self {
    //     let two_pow_n_times_64 = crate::const_helpers::RBuffer::<N>([0u64; N], 1);
    //     const_modulo!(two_pow_n_times_64, self)
    // }

    // pub const fn montgomery_r2(&self) -> Self {
    //     let two_pow_n_times_64_square =
    //         crate::const_helpers::R2Buffer::<N>([0u64; N], [0u64; N], 1);
    //     const_modulo!(two_pow_n_times_64_square, self)
    // }
}

impl<const N: usize> BigInteger for BigInt<N> {
    const NUM_LIMBS: usize = N;
    fn add_with_carry(&mut self, other: &Self) -> bool {
        {
            use arithmetic::adc_for_add_with_carry as adc;

            let a = &mut self.0;
            let b = &other.0;
            let mut carry = 0;

            if N >= 1 {
                carry = adc(&mut a[0], b[0], carry);
            }
            if N >= 2 {
                carry = adc(&mut a[1], b[1], carry);
            }
            if N >= 3 {
                carry = adc(&mut a[2], b[2], carry);
            }
            if N >= 4 {
                carry = adc(&mut a[3], b[3], carry);
            }
            if N >= 5 {
                carry = adc(&mut a[4], b[4], carry);
            }
            if N >= 6 {
                carry = adc(&mut a[5], b[5], carry);
            }
            for i in 6..N {
                carry = adc(&mut a[i], b[i], carry);
            }
            carry != 0
        }
    }

    #[inline]
    fn sub_with_borrow(&mut self, other: &Self) -> bool {
        use arithmetic::sbb_for_sub_with_borrow as sbb;

        let a = &mut self.0;
        let b = &other.0;
        let mut borrow = 0u8;

        if N >= 1 {
            borrow = sbb(&mut a[0], b[0], borrow);
        }
        if N >= 2 {
            borrow = sbb(&mut a[1], b[1], borrow);
        }
        if N >= 3 {
            borrow = sbb(&mut a[2], b[2], borrow);
        }
        if N >= 4 {
            borrow = sbb(&mut a[3], b[3], borrow);
        }
        if N >= 5 {
            borrow = sbb(&mut a[4], b[4], borrow);
        }
        if N >= 6 {
            borrow = sbb(&mut a[5], b[5], borrow);
        }
        for i in 6..N {
            borrow = sbb(&mut a[i], b[i], borrow);
        }
        borrow != 0
    }

    #[inline]
    #[allow(unused)]
    fn mul2(&mut self) -> bool {
        let mut last = 0;
        for i in 0..N {
            let a = &mut self.0[i];
            let tmp = *a >> 63;
            *a <<= 1;
            *a |= last;
            last = tmp;
        }
        last != 0
    }

    // fn muln(&mut self, mut n: u32) {
    //     if n >= (64 * N) as u32 {
    //         *self = Self::from(0u64);
    //         return;
    //     }

    //     while n >= 64 {
    //         let mut t = 0;
    //         for i in 0..N {
    //             core::mem::swap(&mut t, &mut self.0[i]);
    //         }
    //         n -= 64;
    //     }

    //     if n > 0 {
    //         let mut t = 0;
    //         #[allow(unused)]
    //         for i in 0..N {
    //             let a = &mut self.0[i];
    //             let t2 = *a >> (64 - n);
    //             *a <<= n;
    //             *a |= t;
    //             t = t2;
    //         }
    //     }
    // }

    fn div2(&mut self) {
        let mut t = 0;
        for i in 0..N {
            let a = &mut self.0[N - i - 1];
            let t2 = *a << 63;
            *a >>= 1;
            *a |= t;
            t = t2;
        }
    }

    // fn divn(&mut self, mut n: u32) {
    //     if n >= (64 * N) as u32 {
    //         *self = Self::from(0u64);
    //         return;
    //     }

    //     while n >= 64 {
    //         let mut t = 0;
    //         for i in 0..N {
    //             core::mem::swap(&mut t, &mut self.0[N - i - 1]);
    //         }
    //         n -= 64;
    //     }

    //     if n > 0 {
    //         let mut t = 0;
    //         #[allow(unused)]
    //         for i in 0..N {
    //             let a = &mut self.0[N - i - 1];
    //             let t2 = *a << (64 - n);
    //             *a >>= n;
    //             *a |= t;
    //             t = t2;
    //         }
    //     }
    // }

    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.iter().all(|&e| e == 0)
    }

    #[inline]
    fn num_bits(&self) -> u32 {
        let mut ret = N as u32 * 64;
        for i in self.0.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
        }

        ret
    }

    #[inline]
    fn get_bit(&self, i: usize) -> bool {
        if i >= 64 * N {
            false
        } else {
            let limb = i / 64;
            let bit = i - (64 * limb);
            (self.0[limb] & (1 << bit)) != 0
        }
    }

    #[inline]
    fn from_bits_be(bits: &[bool]) -> Self {
        let mut res = Self::default();
        let mut acc: u64 = 0;

        let mut bits = bits.to_vec();
        bits.reverse();
        for (i, bits64) in bits.chunks(64).enumerate() {
            for bit in bits64.iter().rev() {
                acc <<= 1;
                acc += *bit as u64;
            }
            res.0[i] = acc;
            acc = 0;
        }
        res
    }

    fn from_bits_le(bits: &[bool]) -> Self {
        let mut res = Self::zero();
        for (bits64, res_i) in bits.chunks(64).zip(&mut res.0) {
            for (i, bit) in bits64.iter().enumerate() {
                *res_i |= (*bit as u64) << i;
            }
        }
        res
    }

    #[inline]
    fn to_bytes_be(&self) -> Vec<u8> {
        let mut le_bytes = self.to_bytes_le();
        le_bytes.reverse();
        le_bytes
    }

    #[inline]
    fn to_bytes_le(&self) -> Vec<u8> {
        let array_map = self.0.iter().map(|limb| limb.to_le_bytes());
        let mut res = Vec::with_capacity(N * 8);
        for limb in array_map {
            res.extend_from_slice(&limb);
        }
        res
    }
}

pub trait BigInteger
{
    const NUM_LIMBS: usize;

    fn add_with_carry(&mut self, other: &Self) -> bool;
    fn sub_with_borrow(&mut self, other: &Self) -> bool;
    fn mul2(&mut self) -> bool;
    // fn muln(&mut self, amt: u32);
    fn div2(&mut self);
    // fn divn(&mut self, amt: u32);
    fn is_odd(&self) -> bool;
    fn is_even(&self) -> bool;
    fn is_zero(&self) -> bool;
    fn num_bits(&self) -> u32;
    fn get_bit(&self, i: usize) -> bool;
    fn from_bits_be(bits: &[bool]) -> Self;
    fn from_bits_le(bits: &[bool]) -> Self;
    fn to_bytes_be(&self) -> Vec<u8>;
    fn to_bytes_le(&self) -> Vec<u8>;
    // fn find_wnaf(&self, w: usize) -> Option<Vec<i64>>;
}
