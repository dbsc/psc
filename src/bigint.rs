/// References
/// arkworks/algebra ff/src/biginteger/mod.rs

macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

#[macro_export]
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
        tmp as u64
    }};
}

macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

use crate::arithmetic;

pub struct BigInt<const N: usize>(pub [u64; N]);

impl<const N: usize> Default for BigInt<N> {
    fn default() -> Self {
        Self([0u64; N])
    }
}

impl<const N: usize> Clone for BigInt<N> {
    fn clone(&self) -> Self {
        Self(self.0)
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

    pub fn shr(&self) -> Self {
        let mut result = self.clone();
        let mut t = 0;
        let mut i = 0;
        while i < N {
            let a = result.0[N - i - 1];
            let t2 = a << 63;
            result.0[N - i - 1] = result.0[N - i - 1] >> 1;
            result.0[N - i - 1] = result.0[N - i - 1] | t;
            t = t2;
            i += 1;
        }
        result
    }

    fn geq(&self, other: &Self) -> bool {
        let mut i = 0;
        while i < N {
            let a = self.0[N - i - 1];
            let b = other.0[N - i - 1];
            if a < b {
                return false;
            } else if a > b {
                return true;
            }
            i += 1;
        }
        true
    }

    pub fn two_adic_valuation(mut self) -> u32 {
        let mut two_adicity = 0;
        assert!(self.const_is_odd());
        self.0[0] = self.0[0] - 1;
        while self.const_is_even() {
            unimplemented!();
            self = self.shr(); // Aeneas does not understand this expression
            two_adicity += 1;
        }
        two_adicity
    }

    pub fn two_adic_coefficient(mut self) -> Self {
        assert!(self.const_is_odd());
        self.0[0] = self.0[0] - 1;
        while self.const_is_even() {
            unimplemented!();
            self = self.shr(); // Aeneas does not understand this expression
        }
        assert!(self.const_is_odd());
        self
    }

    pub fn divide_by_2_round_down(mut self) -> Self {
        if self.const_is_odd() {
            self.0[0] = self.0[0] - 1;
        }
        self.shr()
    }

    pub const fn const_num_bits(self) -> u32 {
        ((N - 1) * 64) as u32 + (64 - self.0[N - 1].leading_zeros())
    }

    pub(crate) const fn const_sub_with_borrow(mut self, other: &Self) -> (Self, bool) {
        let mut borrow = 0;
        let mut i = 0;
        while i < N {
            self.0[i] = sbb!(self.0[i], other.0[i], &mut borrow);
            i += 1;
        }
        (self, borrow != 0)
    }

    pub(crate) const fn const_add_with_carry(mut self, other: &Self) -> (Self, bool) {
        let mut carry = 0;
        let mut i = 0;
        while i < N {
            self.0[i] = adc!(self.0[i], other.0[i], &mut carry);
            i += 1;
        }

        (self, carry != 0)
    }

    const fn const_mul2_with_carry(mut self) -> (Self, bool) {
        let mut last = 0;
        let mut i = 0;
        while i < N {
            let a = self.0[i];
            let tmp = a >> 63;
            self.0[i] = self.0[i] << 1;
            self.0[i] = self.0[i] | last;
            last = tmp;
        }
        (self, last != 0)
    }

    pub(crate) const fn const_is_zero(&self) -> bool {
        let mut is_zero = true;
        let mut i = 0;
        while i < N {
            is_zero = is_zero && (self.0[i] == 0);
            i += 1;
        }
        is_zero
    }

    pub const fn montgomery_r(&self) -> Self {
        unimplemented!();
    }

    pub const fn montgomery_r2(&self) -> Self {
        unimplemented!();
    }
}

impl<const N: usize> BigInteger for BigInt<N> {
    fn add_with_carry(&mut self, other: &Self) -> bool {
        let mut carry = 0;
        let mut i = 0;
        while i < N {
            carry = arithmetic::adc_for_add_with_carry(&mut self.0[i], other.0[i], carry);
            i += 1;
        }
        carry != 0
    }

    fn sub_with_borrow(&mut self, other: &Self) -> bool {
        let mut borrow = 0;
        let mut i = 0;
        while i < N {
            borrow = arithmetic::sbb_for_sub_with_borrow(&mut self.0[i], other.0[i], borrow);
            i += 1;
        }
        borrow != 0
    }

    fn mul2(&mut self) -> bool {
        let mut last = 0;
        let mut i = 0;
        while i < N {
            let a = &mut self.0[i];
            let tmp = *a >> 63;
            *a <<= 1;
            *a |= last;
            last = tmp;
            i += 1;
        }
        last != 0
    }

    fn muln(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::zero();
            return;
        }

        while n >= 64 { // Aeneas does not understand this loop
            unimplemented!();
            let mut t = 0;
            let mut i = 0;
            while i < N {
                let tmp = t;
                t = self.0[i];
                self.0[i] = tmp;
                i += 1;
            }
            n -= 64;
        }

        if n > 0 { // Aeneas does not understand this
            unimplemented!();
            let mut t = 0;
            let mut i = 0;
            while i < N {
                let a = &mut self.0[i];
                let t2 = *a >> (64 - n);
                *a <<= n;
                *a |= t;
                t = t2;
                i += 1;
            }
        }
    }

    fn mul(&self, other: &Self) -> (Self, Self) {
        if self.const_is_zero() || other.const_is_zero() {
            return (Self::zero(), Self::zero());
        }

        let mut b0 = Self::zero();
        let mut b1 = Self::zero();
        let mut carry = 0;

        let mut i = 0;
        while i < N { // Double loop compilation error
            unimplemented!();
            let mut j = 0;
            while j < N {
                let index = i + j;
                if index < N {
                    b0.0[index] = mac_with_carry!(b0.0[index], self.0[i], other.0[j], &mut carry);
                } else {
                    b1.0[index] = mac_with_carry!(b1.0[index], self.0[i], other.0[j], &mut carry);
                }
                j += 1;
            }
            i += 1;
        }

        (b0, b1)
    }

    fn mul_low(&self, other: &Self) -> Self {
        if self.const_is_zero() || other.const_is_zero() {
            return Self::zero();
        }
        unimplemented!() // Must complete the rest of this code
    }

    fn mul_high(&self, other: &Self) -> Self {
        unimplemented!();
        // self.mul(other).1
    }

    fn div2(&mut self) {
        let mut t = 0;
        let mut i = N - 1;
        while i >= 0 {
            let t2 = self.0[i] << 63;
            self.0[i] = self.0[i] >> 1;
            self.0[i] = self.0[i] | t;
            i -= 1;
        }
    }

    fn divn(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::zero();
            return;
        }

        while n >= 64 { // Aeneas does not understand this
            unimplemented!();
            let mut t = 0;
            let mut i = 0;
            while i < N {
                let tmp = t;
                t = self.0[N - i - 1];
                self.0[N - i - 1] = tmp;
                i += 1;
            }
            n -= 64;
        }

        if n > 0 { // Aeneas does not understand this
            unimplemented!();
            let mut t = 0;
            let mut i = 0;
            while i < N {
                let a = &mut self.0[N - i - 1];
                let t2 = *a << (64 - n);
                *a >>= n;
                *a |= t;
                t = t2;
            }
        }
    }

    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    fn is_zero(&self) -> bool {
        let mut is_zero = true;
        let mut i = 0;
        while i < N {
            is_zero = is_zero && (self.0[i] == 0);
            i += 1;
        }
        is_zero
    }

    fn num_bits(&self) -> u32 {
        let mut ret = N as u32 * 64;
        let mut i = N - 1;
        while i >= 0 {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
            i -= 1;
        }
        ret
    }

    fn get_bit(&self, i: usize) -> bool {
        if i >= 64 * N {
            false
        } else {
            let limb = i / 64;
            let bit = i - (64 * limb);
            (self.0[limb] & (1 << bit)) != 0
        }
    }

    fn from_bits_be(bits: &[bool]) -> Self {
        let mut bits = bits.to_vec();
        bits.reverse();
        Self::from_bits_le(&bits)
    }

    fn from_bits_le(bits: &[bool]) -> Self {
        let mut res = Self::zero();
        let mut i = 0;
        while i < N { // For some reason this loop breaks aeneas
            unimplemented!();
            let mut j = 0;
            while j < 64 {
                let tmp = (bits[64 * i + j] as u64) << i;
                res.0[i] = res.0[i] | tmp;
                j += 1;
            }
            i += 1;
        }
        res
    }

    fn to_bytes_be(&self) -> Vec<u8> {
        let mut le_bytes = self.to_bytes_le();
        le_bytes.reverse();
        le_bytes
    }

    fn to_bytes_le(&self) -> Vec<u8> {
        let mut i = 0;
        let mut res = Vec::with_capacity(N * 8);
        while i < N { // Fails because of `extend_from_slice` method
            let limb = self.0[i].to_le_bytes();
            unimplemented!();
            res.extend_from_slice(&limb);
            i += 1;
        }
        res
    }
}

pub trait BigInteger:
    Sized
{
    fn add_with_carry(&mut self, other: &Self) -> bool;
    fn sub_with_borrow(&mut self, other: &Self) -> bool;
    fn mul2(&mut self) -> bool;
    fn muln(&mut self, amt: u32);
    fn mul(&self, other: &Self) -> (Self, Self);
    fn mul_low(&self, other: &Self) -> Self;
    fn mul_high(&self, other: &Self) -> Self;
    fn div2(&mut self);
    fn divn(&mut self, amt: u32);
    fn is_odd(&self) -> bool;
    fn is_even(&self) -> bool;
    fn is_zero(&self) -> bool;
    fn num_bits(&self) -> u32;
    fn get_bit(&self, i: usize) -> bool;
    fn from_bits_be(bits: &[bool]) -> Self;
    fn from_bits_le(bits: &[bool]) -> Self;
    fn to_bytes_be(&self) -> Vec<u8>;
    fn to_bytes_le(&self) -> Vec<u8>;
}
