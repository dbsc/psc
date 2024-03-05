/// References
/// arkworks/algebra ff/src/biginteger/arithmetic.rs

macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

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

macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
        tmp as u64
    }};
}

pub fn sbb(a: &mut u64, b: u64, borrow: u64) -> u64 {
    let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
    *a = tmp as u64;
    let tmp = tmp >> 64 == 0;
    tmp as u64
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

macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

macro_rules! mac {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}
