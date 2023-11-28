const N: usize = 4;

// pub struct BigInt([u64; 4]);

pub struct BigInt{
    num: [u64; 4]
}

// impl<const N: usize> Default for BigInt<N> {
//     fn default() -> Self {
//         Self([0u64; N])
//     }
// }

fn default() -> BigInt {
    BigInt{num: [0u64; 4]}
    // BigInt([0u64; 4])
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
        let shift: u128 = 1024 * 1024 * 1024 * 1024 * 1024 * 1024 * 16;
        (tmp / shift) as u8 // (tmp >> 64) as u8
    }
}



fn add_with_carry(sself: &mut BigInt, other: &BigInt) -> bool {
    {
        use adc_for_add_with_carry as adc;

        let a = &mut sself.num;
        let b = &other.num;
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
        // for i in 6..N {
        //     carry = adc(&mut a[i], b[i], carry);
        // }
        carry != 0
    }
}