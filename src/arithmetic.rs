/// References
/// arkworks/algebra ff/src/biginteger/arithmetic.rs

// macro_rules! adc {
//     ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
//         let tmp = ($a as u128) + ($b as u128) + ($carry as u128);
//         $carry = (tmp >> 64) as u64;
//         tmp as u64
//     }};
// }

pub fn adc(a: &mut u64, b: u64, carry: u64) -> u64 {
    let tmp = *a as u128 + b as u128 + carry as u128;
    *a = tmp as u64;
    (tmp >> 64) as u64
}

pub fn adc_for_add_with_carry(a: &mut u64, b: u64, carry: u8) -> u8 {
    let tmp = *a as u128 + b as u128 + carry as u128;
    *a = tmp as u64;
    (tmp >> 64) as u8
}

pub fn adc_no_carry(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = a as u128 + b as u128 + *carry as u128;
    tmp as u64
}

// macro_rules! sbb {
//     ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
//         let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
//         $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
//         tmp as u64
//     }};
// }

pub fn sbb(a: &mut u64, b: u64, borrow: u64) -> u64 {
    let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
    *a = tmp as u64;
    (tmp >> 64 == 0) as u64
}

pub fn sbb_for_sub_with_borrow(a: &mut u64, b: u64, borrow: u8) -> u8 {
    let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
    *a = tmp as u64;
    u8::from(tmp >> 64 == 0)
}

pub fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + (b as u128 * c as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

pub fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (a as u128) + (b as u128 * c as u128);
    *carry = (tmp >> 64) as u64;
}

// macro_rules! mac_with_carry {
//     ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
//         let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);
//         $carry = (tmp >> 64) as u64;
//         tmp as u64
//     }};
// }

// macro_rules! mac {
//     ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
//         let tmp = ($a as u128) + ($b as u128 * $c as u128);
//         $carry = (tmp >> 64) as u64;
//         tmp as u64
//     }};
// }

pub fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + (b as u128 * c as u128) + (*carry as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

pub fn find_naf(num: &[u64]) -> Vec<i8> {
    let is_zero = |num: &[u64]| num.iter().all(|x| *x == 0u64);
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    let sub_noborrow = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut borrow = 0;

        for (a, b) in num.iter_mut().zip(other) {
            borrow = sbb(a, b, borrow);
        }
    };
    let add_nocarry = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut carry = 0;

        for (a, b) in num.iter_mut().zip(other) {
            carry = adc(a, b, carry);
        }
    };
    let div2 = |num: &mut [u64]| {
        let mut t = 0;
        for i in num.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    };

    let mut num = num.to_vec();
    let mut res = vec![];

    while !is_zero(&num) {
        let z: i8;
        if is_odd(&num) {
            z = 2 - (num[0] % 4) as i8;
            if z >= 0 {
                sub_noborrow(&mut num, z as u64)
            } else {
                add_nocarry(&mut num, (-z) as u64)
            }
        } else {
            z = 0;
        }
        res.push(z);
        div2(&mut num);
    }

    res
}

pub fn find_relaxed_naf(num: &[u64]) -> Vec<i8> {
    let mut res = find_naf(num);

    let len = res.len();
    if res[len - 2] == 0 && res[len - 3] == -1 {
        res[len - 3] = 1;
        res[len - 2] = 1;
        res.resize(len - 1, 0);
    }

    res
}
