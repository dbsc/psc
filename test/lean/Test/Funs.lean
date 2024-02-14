-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [test]: function definitions
import Base
import Test.Types
open Primitives

namespace test

/- [test::arithmetics::{test::arithmetics::BigInt<N>}::default]:
   Source: 'src/arithmetics.rs', lines 13:4-13:24 -/
def arithmetics.BigInt.default (N : Usize) : Result (arithmetics.BigInt N) :=
  let a := Array.repeat U64 N 0#u64
  Result.ret { num := a }

/- Trait implementation: [test::arithmetics::{test::arithmetics::BigInt<N>}]
   Source: 'src/arithmetics.rs', lines 12:0-12:42 -/
def core.default.DefaulttestarithmeticsBigIntNInst (N : Usize) :
  core.default.Default (arithmetics.BigInt N) := {
  default := arithmetics.BigInt.default N
}

/- [test::arithmetics::adc_for_add_with_carry]:
   Source: 'src/arithmetics.rs', lines 30:0-30:67 -/
def arithmetics.adc_for_add_with_carry
  (a : U64) (b : U64) (carry : U8) : Result (U8 × U64) :=
  do
  let i ← Scalar.cast .U128 a
  let i1 ← Scalar.cast .U128 b
  let i2 ← i + i1
  let i3 ← Scalar.cast .U128 carry
  let tmp ← i2 + i3
  let a1 ← Scalar.cast .U64 tmp
  let i4 ← tmp >>> 64#i32
  let i5 ← Scalar.cast .U8 i4
  Result.ret (i5, a1)

/- [test::arithmetics::{test::arithmetics::BigInt<N>#1}::add_with_carry]: loop 0:
   Source: 'src/arithmetics.rs', lines 78:4-114:5 -/
divergent def arithmetics.BigInt.add_with_carry_loop
  (N : Usize) (a : Array U64 N) (b : Array U64 N) (carry : U8) (i : Usize) :
  Result (Bool × (Array U64 N))
  :=
  if i < N
  then
    do
    let (i1, index_mut_back) ← Array.index_mut_usize U64 N a i
    let i2 ← Array.index_usize U64 N b i
    let (carry1, i3) ← arithmetics.adc_for_add_with_carry i1 i2 carry
    let i4 ← i + 1#usize
    let a1 ← index_mut_back i3
    arithmetics.BigInt.add_with_carry_loop N a1 b carry1 i4
  else Result.ret (carry != 0#u8, a)

/- [test::arithmetics::{test::arithmetics::BigInt<N>#1}::add_with_carry]:
   Source: 'src/arithmetics.rs', lines 78:4-78:54 -/
def arithmetics.BigInt.add_with_carry
  (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N) :
  Result (Bool × (arithmetics.BigInt N))
  :=
  do
  let (b, back) ←
    arithmetics.BigInt.add_with_carry_loop N self.num other.num 0#u8 0#usize
  Result.ret (b, { num := back })

/- Trait implementation: [test::arithmetics::{test::arithmetics::BigInt<N>#1}]
   Source: 'src/arithmetics.rs', lines 74:0-74:45 -/
def test.arithmetics.BigIntegertestarithmeticsBigIntNInst (N : Usize) :
  arithmetics.BigInteger (arithmetics.BigInt N) := {
  add_with_carry := arithmetics.BigInt.add_with_carry N
}

end test
