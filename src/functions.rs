pub fn min(x: u32, y: u32) -> u32 {
    return if x < y { x } else { y };
}

pub fn abs(x: i32) -> i32 {
    return if x < 0 { -x } else { x };
}

pub fn mul2_add1(x: u32) -> u32 {
    return 2 * x + 1;
}
