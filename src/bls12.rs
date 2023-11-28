

pub struct Fp {
    factor: u64,
    pub num: u64,
}

fn zero() -> Fp {
    return Fp {
        factor: 13,
        num: 0
    }
}

fn check_factor(left: &Fp, right: &Fp) {
    if left.factor != right.factor {
        panic!();
    }
}

pub fn add(left: &Fp, right: &Fp) -> Fp {
    check_factor(left, right);
    Fp {
        factor: left.factor,
        num: (left.num + right.num) % left.factor
    }
}

pub fn mul(left: &Fp, right: &Fp) -> Fp {
    check_factor(left, right);
    Fp {
        factor: left.factor,
        num: (left.num * right.num) % left.factor
    }
}

pub fn minus(elem: &Fp) -> Fp {
    Fp {
        factor: elem.factor,
        num: (elem.factor - elem.num) % elem.factor
    }
}

pub fn sub(left: &Fp, right: &Fp) -> Fp {
    check_factor(left, right);
    let minus_right = minus(right);
    add(left, &minus_right)
}

//bool is "isPointAtInfinity"
pub type G1 = (Fp, Fp, bool);
pub type Fp2 = (Fp, Fp); //(10, 8) = (10+8u) : u² = -1
pub type G2 = (Fp2, Fp2, bool);
pub type Fp6 = (Fp2, Fp2, Fp2); //v³ = u + 1
pub type Fp12 = (Fp6, Fp6); //w² = v


/* Arithmetic for FP2 elements */
pub fn fp2fromfp(n: Fp) -> Fp2 {
    (n, zero())
}

pub fn fp2zero() -> Fp2 {
    fp2fromfp(zero())
}

pub fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (sub(&zero(), &n1), sub(&zero(), &n2))
}

pub fn fp2add(n: Fp2, m: Fp2) -> Fp2 {
    //Coordinate wise
    let (n1, n2) = n;
    let (m1, m2) = m;
    (add(&n1, &m1), add(&n2, &m2))
}

pub fn fp2sub(n: Fp2, m: Fp2) -> Fp2 {
    fp2add(n, fp2neg(m))
}

pub fn fp2mul(n: Fp2, m: Fp2) -> Fp2 {
    //(a+bu)*(c+du) = ac + adu + bcu + bdu^2 = ac - bd + (ad + bc)u
    let (n1, n2) = n;
    let (m1, m2) = m;
    let x1 = sub(&mul(&n1, &m1), &mul(&n2, &m2));
    let x2 = add(&mul(&n1, &m2), &mul(&n2, &m1));
    (x1, x2)
}

// pub fn fp2inv(n: Fp2) -> Fp2 {
//     let (n1, n2) = n;
//     let t0 = add(&mul(&n1, &n1), &mul(&n2, &n2));
//     let t1 = t0.inv();
//     let x1 = n1 * t1;
//     let x2 = sub(&zero(), &mul(&n2, &t1));
//     (x1, x2)
// }

// pub fn fp2conjugate(n: Fp2) -> Fp2 {
//     let (n1, n2) = n;
//     (n1, sub(&zero(), &n2))
// }

// impl FiniteField {
//     const MODULUS: u64 = 13;

//     pub fn new(num: u64) -> Self {
//         Self {
//             num: num % Self::MODULUS
//         }
//     }

//     pub fn add(&self, other: FiniteField) -> Self {
//         Self {
//             num: (self.num + other.num) % Self::MODULUS
//         }
//     }
// }

// // use PartialEq trait to check whether two fields are equal or not
// impl PartialEq for FiniteField {
//     fn eq(&self, other: &FiniteField) -> bool {
//         self.num == other.num
//     }
// }

// impl Eq for FiniteField {}


// impl Add<FiniteField> for FiniteField {
//     type Output = FiniteField;

//     fn add(self, other: FiniteField) -> FiniteField {
//         return Self{num: self.num + other.num % Self::MODULUS};
//     }
// }

// impl Mul<FiniteField> for FiniteField {
//     type Output = FiniteField;

//     fn mul(self, other: FiniteField) -> FiniteField {
//         return Self{num: (self.num * other.num) % Self::MODULUS};
//     }
// }

// impl Sub<FiniteField> for FiniteField {
//     type Output = FiniteField;

//     fn sub(self, other: FiniteField) -> FiniteField {
//         return Self{num: (self.num - other.num) % Self::MODULUS};
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_compare_two_field_elements() {
//         let a = FiniteField::new(14);
//         let b = FiniteField::new(1);

//         assert_eq!(a.num, b.num);
//     }

//     #[test]
//     fn test_add_two_field_elements() {
//         let a = FiniteField::new(14);
//         let b = FiniteField::new(1);
//         let c = FiniteField::new(2);

//         assert_eq!(a.num, b.num);
//         assert_eq!(a.add(b).num, c.num);
//     }
// }