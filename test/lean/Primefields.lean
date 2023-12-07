namespace Primitives



def add_Primitives(base a b:Nat):Nat:=
Id.run do
let c:Nat := a+b
return (c % base)

def subtract_Primitives(base a b:Nat):Nat:=
if a>b then
Id.run do
let c:Nat:= a-b
return c
else
Id.run do
let c:Nat:=a+base-b
return c

def mult_Primitives(base a b:Nat):Nat:=
Id.run do
let c:Nat:= a*b
return c % base

def inv_Primitives(base a:Nat):Nat:=
Id.run do
return (a^(base-2))%base

def div_Primitives(base a b:Nat):Nat:=
Id.run do
let d:Nat := inv_Primitives base b
let c:Nat:= mult_Primitives base a d
return c % base

example :∀a: Nat ,∀b:Nat, ∀ base:Nat, base>0 → add_Primitives base a b <base:=
by
intro a₁ b₁ base h₁
rw [add_Primitives]
simp
apply Nat.mod_lt (a₁+b₁)
exact h₁

example : ∀ a:Nat, ∀ b:Nat, ∀ c:Nat, ∀ base:Nat, add_Primitives base a (add_Primitives base b c)=add_Primitives base (add_Primitives base a b) c:=
by
intro a₁ b₁ c₁ base₁
rw [add_Primitives]
simp
rw [add_Primitives]
simp
rw [add_Primitives]
simp
rw [add_Primitives]
simp
sorry
