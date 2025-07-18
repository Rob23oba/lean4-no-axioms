import NoAxioms.Prelude

class HAddCongr (α : Type u) (β : Type v) {γ : Type w} [Eqv α] [Eqv β] [Eqv γ] [HAdd α β γ] where
  add_congr {x₁ x₂ : α} {y₁ y₂ : β} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ + y₁ ~= x₂ + y₂

class HSubCongr (α : Type u) (β : Type v) {γ : Type w} [Eqv α] [Eqv β] [Eqv γ] [HSub α β γ] where
  sub_congr {x₁ x₂ : α} {y₁ y₂ : β} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ - y₁ ~= x₂ - y₂

class HMulCongr (α : Type u) (β : Type v) {γ : Type w} [Eqv α] [Eqv β] [Eqv γ] [HMul α β γ] where
  mul_congr {x₁ x₂ : α} {y₁ y₂ : β} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ * y₁ ~= x₂ * y₂

class HDivCongr (α : Type u) (β : Type v) {γ : Type w} [Eqv α] [Eqv β] [Eqv γ] [HDiv α β γ] where
  div_congr {x₁ x₂ : α} {y₁ y₂ : β} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ / y₁ ~= x₂ / y₂

class AddCongr (α : Type u) [Eqv α] [Add α] extends HAddCongr α α
class SubCongr (α : Type u) [Eqv α] [Sub α] extends HSubCongr α α
class MulCongr (α : Type u) [Eqv α] [Mul α] extends HMulCongr α α
class DivCongr (α : Type u) [Eqv α] [Div α] extends HDivCongr α α

class NegCongr (α : Type u) [Eqv α] [Neg α] where
  neg_congr {x₁ x₂ : α} (hx : x₁ ~= x₂) : -x₁ ~= -x₂

class InvCongr (α : Type u) [Eqv α] [Inv α] where
  inv_congr {x₁ x₂ : α} (hx : x₁ ~= x₂) : x₁⁻¹ ~= x₂⁻¹

class LECongr (α : Type u) [Eqv α] [LE α] where
  le_congr {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂

@[ccongr]
theorem LECongr.ge_congr {α : Type u} [Eqv α] {_ : LE α} [LECongr α]
    {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ≥ y₁ ↔ x₂ ≥ y₂ :=
  LECongr.le_congr hy hx

class LTCongr (α : Type u) [Eqv α] [LT α] where
  lt_congr {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ < y₁ ↔ x₂ < y₂

@[ccongr]
theorem LTCongr.gt_congr {α : Type u} [Eqv α] {_ : LT α} [LTCongr α]
    {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ > y₁ ↔ x₂ > y₂ :=
  LTCongr.lt_congr hy hx

export HAddCongr (add_congr)
export HSubCongr (sub_congr)
export HMulCongr (mul_congr)
export HDivCongr (div_congr)
export NegCongr (neg_congr)
export InvCongr (inv_congr)
export LECongr (le_congr ge_congr)
export LTCongr (lt_congr gt_congr)

attribute [ccongr] add_congr sub_congr mul_congr div_congr
  neg_congr inv_congr le_congr lt_congr

@[ccongr]
theorem Nat.cast_congr {α : Type u} [Eqv α] [NatCast α] {n₁ n₂ : Nat} (hn : n₁ ~= n₂) :
    (n₁ : α) ~= (n₂ : α) := by
  cases hn; rfl

class Nontrivial (α : Type u) [Eqv α] where
  exists_pair_ne : ∃' x y : α, x ~!= y

class Monoid (α : Type u) [Eqv α] extends Mul α, MulCongr α, One α where
  mul_one (x : α) : x * 1 ~= x
  one_mul (x : α) : 1 * x ~= x
  mul_assoc (x y z : α) : x * y * z ~= x * (y * z)

class AddMonoid (α : Type u) [Eqv α] extends Add α, AddCongr α, Zero α where
  add_zero (x : α) : x + 0 ~= x
  zero_add (x : α) : 0 + x ~= x
  add_assoc (x y z : α) : x + y + z ~= x + (y + z)

@[cnsimp]
theorem mul_one [Eqv α] [Monoid α] (x : α) : x * 1 ~= x := Monoid.mul_one x

@[cnsimp]
theorem add_zero [Eqv α] [AddMonoid α] (x : α) : x + 0 ~= x := AddMonoid.add_zero x

@[cnsimp]
theorem one_mul [Eqv α] [Monoid α] (x : α) : 1 * x ~= x := Monoid.one_mul x

@[cnsimp]
theorem zero_add [Eqv α] [AddMonoid α] (x : α) : 0 + x ~= x := AddMonoid.zero_add x

theorem mul_assoc [Eqv α] [Monoid α] (x y z : α) : x * y * z ~= x * (y * z) :=
  Monoid.mul_assoc x y z

theorem add_assoc [Eqv α] [AddMonoid α] (x y z : α) : x + y + z ~= x + (y + z) :=
  AddMonoid.add_assoc x y z

class DivInvMonoid (α : Type u) [Eqv α] extends Monoid α, Inv α, Div α, InvCongr α, DivCongr α where
  div_eq_mul_inv (x y : α) : x / y ~= x * y⁻¹

class SubNegMonoid (α : Type u) [Eqv α] extends AddMonoid α, Neg α, NegCongr α, Sub α, SubCongr α where
  sub_eq_add_neg (x y : α) : x - y ~= x + -y

theorem div_eq_mul_inv [Eqv α] [DivInvMonoid α] (x y : α) : x / y ~= x * y⁻¹ :=
  DivInvMonoid.div_eq_mul_inv x y

theorem sub_eq_add_neg [Eqv α] [SubNegMonoid α] (x y : α) : x - y ~= x + -y :=
  SubNegMonoid.sub_eq_add_neg x y

class MonoidWithZero (α : Type u) [Eqv α] extends Monoid α, Zero α where
  mul_zero (x : α) : x * 0 ~= 0
  zero_mul (x : α) : 0 * x ~= 0

@[cnsimp]
theorem mul_zero [Eqv α] [MonoidWithZero α] (x : α) : x * 0 ~= 0 :=
  MonoidWithZero.mul_zero x

@[cnsimp]
theorem zero_mul [Eqv α] [MonoidWithZero α] (x : α) : 0 * x ~= 0 :=
  MonoidWithZero.zero_mul x

class GroupWithZero (α : Type u) [Eqv α] extends MonoidWithZero α, DivInvMonoid α, Nontrivial α where
  inv_zero : (0 : α)⁻¹ ~= 0
  inv_mul_cancel (x : α) (h : x ~!= 0) : x⁻¹ * x ~= 1

class AddGroup (α : Type u) [Eqv α] extends SubNegMonoid α where
  neg_add_cancel (x : α) : -x + x ~= 0

theorem inv_mul_cancel [Eqv α] [GroupWithZero α] {x : α} (h : x ~!= 0) : x⁻¹ * x ~= 1 :=
  GroupWithZero.inv_mul_cancel x h

@[cnsimp]
theorem neg_add_cancel [Eqv α] [AddGroup α] (x : α) : -x + x ~= 0 := AddGroup.neg_add_cancel x

@[cnsimp]
theorem inv_zero [Eqv α] [GroupWithZero α] : (0 : α)⁻¹ ~= 0 :=
  GroupWithZero.inv_zero

theorem zero_ne_one [Eqv α] [MonoidWithZero α] [Nontrivial α] : (0 : α) ~!= 1 := by
  intro h
  have : ∃' x y : α, x ~!= y := Nontrivial.exists_pair_ne
  refine this.elim fun a ha => ha.elim fun b hb => ?_
  apply hb
  calc
    a ~= a * 1 := by cnsimp
    _ ~= 0 := by cnsimp only [← h, mul_zero, eq'_self_iff]
    _ ~= b * 1 := by cnsimp only [← h, mul_zero, eq'_self_iff]
    _ ~= b := by cnsimp

theorem inv_eq_of_mul_eq_one [Eqv α] [GroupWithZero α] {x y : α} (h : x * y ~= 1) : x⁻¹ ~= y := by
  have hx : x ~!= 0 := by
    intro hx
    cnsimp only [hx, zero_mul] at h
    exact zero_ne_one h
  calc
    x⁻¹ ~= x⁻¹ * (x * y) := by cnsimp [h]
    _ ~= y := by cnsimp [← mul_assoc, inv_mul_cancel hx]

theorem neg_eq_of_add_eq_zero [Eqv α] [AddGroup α] {x y : α} (h : x + y ~= 0) : -x ~= y := by
  calc
    -x ~= -x + (x + y) := by cnsimp [h]
    _ ~= y := by cnsimp [← add_assoc]

theorem inv_eq_zero_iff [Eqv α] [GroupWithZero α] {x : α} : x⁻¹ ~= 0 ↔ x ~= 0 := by
  constructor
  · intro h
    by_contra' h'
    have : x⁻¹ * x ~= 1 := inv_mul_cancel h'
    cnsimp only [h, zero_mul] at this
    apply h'
    calc
      x ~= x * 1 := by cnsimp
      _ ~= 0 := by cnsimp only [← this, mul_zero, eq'_self_iff]
  · intro h
    cnsimp [h]

@[cnsimp]
theorem inv_inv [Eqv α] [GroupWithZero α] (x : α) : x⁻¹⁻¹ ~= x := by
  by_cases' h : x ~= 0
  · cnsimp [h]
  calc
    x⁻¹⁻¹ ~= x⁻¹⁻¹ * (x⁻¹ * x) := by cnsimp only [inv_mul_cancel h, mul_one, eq'_self_iff]
    _ ~= (x⁻¹⁻¹ * x⁻¹) * x := by cnsimp only [mul_assoc, eq'_self_iff]
    _ ~= x := by cnsimp only [inv_mul_cancel (inv_eq_zero_iff.not.mpr h), one_mul, eq'_self_iff]

@[cnsimp]
theorem neg_neg [Eqv α] [AddGroup α] (x : α) : -(-x) ~= x := by
  calc
    -(-x) ~= -(-x) + (-x + x) := by cnsimp only [neg_add_cancel, add_zero, eq'_self_iff]
    _ ~= (-(-x) + -x) + x := by cnsimp only [add_assoc, eq'_self_iff]
    _ ~= x := by cnsimp only [neg_add_cancel, zero_add, eq'_self_iff]

theorem mul_inv_cancel [Eqv α] [GroupWithZero α] {x : α} (h : x ~!= 0) : x * x⁻¹ ~= 1 := by
  calc
    x * x⁻¹ ~= x⁻¹⁻¹ * x⁻¹ := by cnsimp only [inv_inv, eq'_self_iff]
    _ ~= 1 := by cnsimp only [inv_mul_cancel (inv_eq_zero_iff.not.mpr h), eq'_self_iff]

@[cnsimp]
theorem add_neg_cancel [Eqv α] [AddGroup α] (x : α) : x + -x ~= 0 := by
  calc
    x + -x ~= -(-x) + -x := by cnsimp only [neg_neg, eq'_self_iff]
    _ ~= 0 := by cnsimp only [neg_add_cancel, eq'_self_iff]

theorem div_self [Eqv α] [GroupWithZero α] {x : α} (h : x ~!= 0) : x / x ~= 1 := by
  cnsimp only [div_eq_mul_inv, mul_inv_cancel h, eq'_self_iff]

@[cnsimp]
theorem sub_self [Eqv α] [AddGroup α] (x : α) : x - x ~= 0 := by
  cnsimp only [sub_eq_add_neg, add_neg_cancel, eq'_self_iff]

theorem mul_div_cancel_right [Eqv α] [GroupWithZero α] {x y : α} (h : y ~!= 0) :
    x * y / y ~= x := by
  cnsimp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel h, mul_one, eq'_self_iff]

@[cnsimp]
theorem add_sub_cancel_right [Eqv α] [AddGroup α] (x y : α) : x + y - y ~= x := by
  cnsimp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero, eq'_self_iff]

theorem div_mul_cancel [Eqv α] [GroupWithZero α] {x y : α} (h : y ~!= 0) :
    x / y * y ~= x := by
  cnsimp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel h, mul_one, eq'_self_iff]

@[cnsimp]
theorem sub_add_cancel [Eqv α] [AddGroup α] (x y : α) : x - y + y ~= x := by
  cnsimp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, eq'_self_iff]

theorem div_mul_assoc [Eqv α] [DivInvMonoid α] (x y z : α) : x * y / z ~= x * (y / z) := by
  cnsimp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, eq'_self_iff]

theorem add_sub_assoc [Eqv α] [AddGroup α] (x y z : α) : x + y - z ~= x + (y - z) := by
  cnsimp only [sub_eq_add_neg, add_assoc, eq'_self_iff]

@[cnsimp]
theorem inv_one [Eqv α] [GroupWithZero α] : (1 : α)⁻¹ ~= 1 := by
  calc
    (1 : α)⁻¹ ~= 1⁻¹ * 1 := (mul_one _).symm
    _ ~= 1 := inv_mul_cancel zero_ne_one.symm

@[cnsimp]
theorem neg_zero [Eqv α] [AddGroup α] : -(0 : α) ~= 0 := by
  calc
    -(0 : α) ~= -0 + 0 := (add_zero _).symm
    _ ~= 0 := neg_add_cancel 0

@[cnsimp]
theorem div_one [Eqv α] [GroupWithZero α] (x : α) : x / 1 ~= x := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem sub_zero [Eqv α] [AddGroup α] (x : α) : x - 0 ~= x := by
  cnsimp [sub_eq_add_neg]

@[cnsimp]
theorem div_zero [Eqv α] [GroupWithZero α] (x : α) : x / 0 ~= 0 := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem zero_div [Eqv α] [GroupWithZero α] (x : α) : 0 / x ~= 0 := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem one_div [Eqv α] [GroupWithZero α] (x : α) : 1 / x ~= x⁻¹ := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem zero_sub [Eqv α] [AddGroup α] (x : α) : 0 - x ~= -x := by
  cnsimp [sub_eq_add_neg]

@[cnsimp]
theorem neg_add_rev [Eqv α] [AddGroup α] (x y : α) : -(x + y) ~= -y + -x := by
  calc
    -(x + y) ~= -(x + y) + (x + (y + -y) + -x) := by cnsimp
    _ ~= -(x + y) + (x + y) + -y + -x := by cnsimp only [add_assoc, eq'_self_iff]
    _ ~= -y + -x := by cnsimp

@[cnsimp]
theorem neg_sub [Eqv α] [AddGroup α] (x y : α) : -(x - y) ~= y - x := by
  cnsimp [sub_eq_add_neg]

@[cnsimp]
theorem sub_neg [Eqv α] [AddGroup α] (x y : α) : x - (-y) ~= x + y := by
  cnsimp [sub_eq_add_neg]

class IsCancelAdd (α : Type u) [Eqv α] [Add α] where
  add_left_cancel (x y z : α) : x + y ~= x + z → y ~= z
  add_right_cancel (x y z : α) : x + z ~= y + z → x ~= y

class IsCancelMulWithZero (α : Type u) [Eqv α] [Mul α] [Zero α] where
  mul_left_cancel (x y z : α) : x ~!= 0 → x * y ~= x * z → y ~= z
  mul_right_cancel (x y z : α) : z ~!= 0 → x * z ~= y * z → x ~= y

instance [Eqv α] [GroupWithZero α] : IsCancelMulWithZero α where
  mul_left_cancel x y z hx h := by
    calc
      y ~= x⁻¹ * x * y := by cnsimp [inv_mul_cancel hx]
      _ ~= x⁻¹ * x * z := by cnsimp [mul_assoc, h]
      _ ~= z := by cnsimp [inv_mul_cancel hx]
  mul_right_cancel x y z hz h := by
    calc
      x ~= x * z / z := by cnsimp [mul_div_cancel_right hz]
      _ ~= y * z / z := by cnsimp [h]
      _ ~= y := by cnsimp [mul_div_cancel_right hz]

instance [Eqv α] [AddGroup α] : IsCancelAdd α where
  add_left_cancel x y z h := by
    calc
      y ~= -x + x + y := by cnsimp
      _ ~= -x + x + z := by cnsimp only [add_assoc, h, eq'_self_iff]
      _ ~= z := by cnsimp
  add_right_cancel x y z h := by
    calc
      x ~= x + z - z := by cnsimp
      _ ~= y + z - z := by cnsimp only [h, eq'_self_iff]
      _ ~= y := by cnsimp

theorem add_left_cancel [Eqv α] [Add α] [IsCancelAdd α] {x y z : α}
    (h : x + y ~= x + z) : y ~= z :=
  IsCancelAdd.add_left_cancel x y z h

theorem add_right_cancel [Eqv α] [Add α] [IsCancelAdd α] {x y z : α}
    (h : x + z ~= y + z) : x ~= y :=
  IsCancelAdd.add_right_cancel x y z h

theorem add_left_cancel_iff [Eqv α] [Add α] [AddCongr α] [IsCancelAdd α] {x y z : α} :
    x + y ~= x + z ↔ y ~= z := by
  constructor
  · exact add_left_cancel
  · intro h
    cnsimp [h]

theorem add_right_cancel_iff [Eqv α] [Add α] [AddCongr α] [IsCancelAdd α] {x y z : α} :
    x + z ~= y + z ↔ x ~= y := by
  constructor
  · exact add_right_cancel
  · intro h
    cnsimp [h]

@[cnsimp]
theorem add_left_inj [Eqv α] [Add α] [AddCongr α] [IsCancelAdd α] {x y : α} (z : α) :
    x + z ~= y + z ↔ x ~= y :=
  add_right_cancel_iff

@[cnsimp]
theorem add_right_inj [Eqv α] [Add α] [AddCongr α] [IsCancelAdd α] (x : α) {y z : α} :
    x + y ~= x + z ↔ y ~= z :=
  add_left_cancel_iff

theorem mul_left_cancel [Eqv α] [Mul α] [Zero α] [IsCancelMulWithZero α] {x y z : α}
    (hx : x ~!= 0) (h : x * y ~= x * z) : y ~= z :=
  IsCancelMulWithZero.mul_left_cancel x y z hx h

theorem mul_right_cancel [Eqv α] [Mul α] [Zero α] [IsCancelMulWithZero α] {x y z : α}
    (hz : z ~!= 0) (h : x * z ~= y * z) : x ~= y :=
  IsCancelMulWithZero.mul_right_cancel x y z hz h

theorem mul_right_cancel_iff [Eqv α] [Mul α] [Zero α] [MulCongr α] [IsCancelMulWithZero α]
    {x y z : α} (h : z ~!= 0) : x * z ~= y * z ↔ x ~= y := by
  constructor
  · exact mul_right_cancel h
  · intro h
    cnsimp [h]

theorem mul_left_cancel_iff [Eqv α] [Mul α] [Zero α] [MulCongr α] [IsCancelMulWithZero α]
    {x y z : α} (h : x ~!= 0) : x * y ~= x * z ↔ y ~= z := by
  constructor
  · exact mul_left_cancel h
  · intro h
    cnsimp [h]

theorem mul_left_inj [Eqv α] [Mul α] [Zero α] [MulCongr α] [IsCancelMulWithZero α]
    {x y z : α} (h : z ~!= 0) : x * z ~= y * z ↔ x ~= y :=
  mul_right_cancel_iff h

theorem mul_right_inj [Eqv α] [Mul α] [Zero α] [MulCongr α] [IsCancelMulWithZero α]
    {x y z : α} (h : x ~!= 0) : x * y ~= x * z ↔ y ~= z :=
  mul_left_cancel_iff h

theorem mul_ne_zero [Eqv α] [MonoidWithZero α] [IsCancelMulWithZero α] {x y : α}
    (hx : x ~!= 0) (hy : y ~!= 0) : x * y ~!= 0 := by
  intro h
  replace h := h.trans (zero_mul y).symm
  replace h := mul_right_cancel hy h
  exact absurd h hx

@[cnsimp]
theorem mul_eq_zero [Eqv α] [MonoidWithZero α] [IsCancelMulWithZero α] {x y : α} :
    x * y ~= 0 ↔ x ~= 0 ∨' y ~= 0 := by
  constructor
  · intro h
    by_contra' h'
    cnsimp at h'
    exact mul_ne_zero h'.1 h'.2 h
  · intro h
    refine h.elim (fun h => ?_) (fun h => ?_) <;> cnsimp [h]

@[cnsimp]
theorem zero_eq_mul [Eqv α] [MonoidWithZero α] [IsCancelMulWithZero α] {x y : α} : 0 ~= x * y ↔ x ~= 0 ∨' y ~= 0 := by
  cnsimp [eq'_comm (x := (0 : α))]

@[cnsimp]
theorem inv_mul_rev [Eqv α] [GroupWithZero α] (x y : α) : (x * y)⁻¹ ~= y⁻¹ * x⁻¹ := by
  by_cases' h : x ~= 0
  · cnsimp [h]
  by_cases' h' : y ~= 0
  · cnsimp [h']
  calc
    (x * y)⁻¹ ~= (x * y)⁻¹ * (x * (y * y⁻¹) * x⁻¹) := by cnsimp [mul_inv_cancel h, mul_inv_cancel h']
    _ ~= (x * y)⁻¹ * (x * y) * y⁻¹ * x⁻¹ := by cnsimp only [mul_assoc, eq'_self_iff]
    _ ~= y⁻¹ * x⁻¹ := by cnsimp [inv_mul_cancel (mul_ne_zero h h')]

@[cnsimp]
theorem inv_div [Eqv α] [GroupWithZero α] (x y : α) : (x / y)⁻¹ ~= y / x := by
  cnsimp [div_eq_mul_inv]

theorem eq_of_div_eq_one [Eqv α] [GroupWithZero α] {x y : α} (h : x / y ~= 1) : x ~= y := by
  have : y ~!= 0 := by
    intro h'
    cnsimp only [h', div_zero] at h
    exact zero_ne_one h
  apply mul_right_cancel (z := y⁻¹) (inv_eq_zero_iff.not.mpr this)
  cnsimp [← div_eq_mul_inv, h, div_self this]

theorem eq_of_sub_eq_zero [Eqv α] [AddGroup α] {x y : α} (h : x - y ~= 0) : x ~= y := by
  apply add_right_cancel (z := -y)
  cnsimp [← sub_eq_add_neg, h]

theorem sub_eq_iff_eq_add [Eqv α] [AddGroup α] {x y z : α} : x - y ~= z ↔ x ~= z + y := by
  have : x - y ~= z  ↔ x - y + y ~= z + y := (add_left_inj y).symm
  cnsimp at this
  exact this

theorem eq_sub_iff_add_eq [Eqv α] [AddGroup α] {x y z : α} : x ~= y - z ↔ x + z ~= y := by
  have : x ~= y - z ↔ x + z ~= y - z + z := (add_left_inj z).symm
  cnsimp at this
  exact this

theorem neg_eq_zero_iff [Eqv α] [AddGroup α] {x : α} : -x ~= 0 ↔ x ~= 0 := by
  calc
    _ ↔ x + -x ~= x + 0 := add_left_cancel_iff.symm
    _ ↔ 0 ~= x := by cnsimp
    _ ↔ x ~= 0 := eq'_comm

class CommMonoid (α : Type u) [Eqv α] extends Monoid α where
  mul_comm (x y : α) : x * y ~= y * x

class AddCommMonoid (α : Type u) [Eqv α] extends AddMonoid α where
  add_comm (x y : α) : x + y ~= y + x

theorem mul_comm [Eqv α] [CommMonoid α] (x y : α) : x * y ~= y * x :=
  CommMonoid.mul_comm x y

theorem add_comm [Eqv α] [AddCommMonoid α] (x y : α) : x + y ~= y + x :=
  AddCommMonoid.add_comm x y

theorem mul_right_comm [Eqv α] [CommMonoid α] (x y z : α) : x * y * z ~= x * z * y := by
  cnsimp only [mul_assoc, mul_comm y, eq'_self_iff]

theorem add_right_comm [Eqv α] [AddCommMonoid α] (x y z : α) : x + y + z ~= x + z + y := by
  cnsimp only [add_assoc, add_comm y, eq'_self_iff]

theorem mul_left_comm [Eqv α] [CommMonoid α] (x y z : α) : x * (y * z) ~= y * (x * z) := by
  cnsimp only [mul_comm y]
  cnsimp only [← mul_assoc, eq'_self_iff]

theorem add_left_comm [Eqv α] [AddCommMonoid α] (x y z : α) : x + (y + z) ~= y + (x + z) := by
  cnsimp only [add_comm y]
  cnsimp only [← add_assoc, eq'_self_iff]

class CommGroupWithZero (α : Type u) [Eqv α] extends GroupWithZero α, CommMonoid α

class AddCommGroup (α : Type u) [Eqv α] extends AddGroup α, AddCommMonoid α

theorem mul_div_cancel [Eqv α] [CommGroupWithZero α] {x : α} (hx : x ~!= 0) (y : α) :
    x * (y / x) ~= y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y, ← mul_assoc, mul_inv_cancel hx]

@[cnsimp]
theorem add_sub_cancel [Eqv α] [AddCommGroup α] (x y : α) : x + (y - x) ~= y := by
  cnsimp [sub_eq_add_neg, add_right_comm x y, ← add_assoc]

theorem mul_div_cancel_left [Eqv α] [CommGroupWithZero α] {x : α} (hx : x ~!= 0) (y : α) :
    x * y / x ~= y := by
  cnsimp [mul_comm x, mul_div_cancel_right hx]

@[cnsimp]
theorem add_sub_cancel_left [Eqv α] [AddCommGroup α] (x y : α) : x + y - x ~= y := by
  cnsimp [add_comm x]

theorem mul_div_comm [Eqv α] [CommGroupWithZero α] (x y z : α) :
    x * y / z ~= x / z * y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y]

theorem add_sub_comm [Eqv α] [AddCommGroup α] (x y z : α) :
    x + y - z ~= x - z + y := by
  cnsimp [sub_eq_add_neg, add_right_comm x y]

theorem div_right_comm [Eqv α] [CommGroupWithZero α] (x y z : α) :
    x / y / z ~= x / z / y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y⁻¹]

theorem sub_right_comm [Eqv α] [AddCommGroup α] (x y z : α) :
    x - y - z ~= x - z - y := by
  cnsimp [sub_eq_add_neg, add_right_comm x (-y)]

theorem div_div [Eqv α] [CommGroupWithZero α] (x y z : α) :
    x / y / z ~= x / (y * z) := by
  cnsimp [div_eq_mul_inv, mul_assoc, mul_comm y⁻¹]

theorem sub_sub [Eqv α] [AddCommGroup α] (x y z : α) :
    x - y - z ~= x - (y + z) := by
  cnsimp [sub_eq_add_neg, add_assoc, add_comm (-y)]

theorem sub_eq_iff_eq_add' [Eqv α] [AddCommGroup α] {x y z : α} : x - y ~= z ↔ x ~= y + z := by
  cnsimp only [add_comm y]
  exact sub_eq_iff_eq_add

@[cnsimp]
theorem add_sub_add_cancel_right [Eqv α] [AddCommGroup α] {x y z : α} :
    (x + y) - (x + z) ~= y - z := by
  cnsimp only [← sub_sub, add_sub_cancel_left, eq'_self_iff]

@[cnsimp]
theorem add_sub_add_cancel_left [Eqv α] [AddCommGroup α] {x y z : α} :
    (x + z) - (y + z) ~= x - y := by
  cnsimp only [← sub_sub, sub_right_comm _ y, add_sub_cancel_right, eq'_self_iff]

class AddMonoidWithOne (α : Type u) [Eqv α] extends NatCast α, AddMonoid α, One α where
  natCast_zero : natCast 0 ~= 0
  natCast_succ (n : Nat) : natCast (n + 1) ~= natCast n + 1

@[cnsimp]
theorem Nat.cast_zero [Eqv α] [AddMonoidWithOne α] : ((0 : Nat) : α) ~= 0 :=
  AddMonoidWithOne.natCast_zero

theorem Nat.cast_succ [Eqv α] [AddMonoidWithOne α] (n : Nat) :
    ((n + 1 : Nat) : α) ~= (n : α) + 1 :=
  AddMonoidWithOne.natCast_succ n

@[cnsimp]
theorem Nat.cast_one [Eqv α] [AddMonoidWithOne α] :
    ((1 : Nat) : α) ~= 1 := by
  cnsimp [Nat.cast_succ, Nat.cast_zero]

@[cnsimp]
theorem Nat.cast_add [Eqv α] [AddMonoidWithOne α] (x y : Nat) :
    ((x + y : Nat) : α) ~= (x + y : α) := by
  induction y with
  | zero => dsimp; cnsimp
  | succ k ih =>
    dsimp only [Nat.add_succ]
    dsimp only [Nat.succ_eq_add_one]
    cnsimp only [Nat.cast_succ, ih, ← add_assoc, eq'_self_iff]

class Nat.AtLeastTwo (n : Nat) where
  out : 2 ≤ n

instance : Nat.AtLeastTwo (n + 2) where
  out := Nat.le_add_left ..

instance (priority := low) instOfNatAtLeastTwo {n : Nat} [NatCast α] [Nat.AtLeastTwo n] :
    OfNat α n where
  ofNat := n.cast

@[cnsimp]
theorem Nat.cast_ofNat [Eqv α] [AddMonoidWithOne α] (n : Nat) [Nat.AtLeastTwo n] :
    (no_index (OfNat.ofNat n : Nat) : α) ~= no_index (OfNat.ofNat n) := by
  rfl

class Semiring (α : Type u) [Eqv α] extends MonoidWithZero α, AddCommMonoid α, AddMonoidWithOne α where
  mul_add (x y z : α) : x * (y + z) ~= x * y + x * z
  add_mul (x y z : α) : (x + y) * z ~= x * z + y * z

class Ring (α : Type u) [Eqv α] extends AddCommGroup α, Semiring α

class CommSemiring (α : Type u) [Eqv α] extends Semiring α, CommMonoid α

class CommRing (α : Type u) [Eqv α] extends Ring α, CommMonoid α

theorem mul_add [Eqv α] [Semiring α] (x y z : α) : x * (y + z) ~= x * y + x * z :=
  Semiring.mul_add x y z

theorem add_mul [Eqv α] [Semiring α] (x y z : α) : (x + y) * z ~= x * z + y * z :=
  Semiring.add_mul x y z

@[cnsimp]
theorem neg_mul [Eqv α] [Ring α] (x y : α) : -x * y ~= -(x * y) := by
  apply add_left_cancel (x := x * y)
  cnsimp [← add_mul]

@[cnsimp]
theorem mul_neg [Eqv α] [Ring α] (x y : α) : x * -y ~= -(x * y) := by
  apply add_left_cancel (x := x * y)
  cnsimp [← mul_add]

theorem mul_sub [Eqv α] [Ring α] (x y z : α) : x * (y - z) ~= x * y - x * z := by
  cnsimp [sub_eq_add_neg, mul_add]

theorem sub_mul [Eqv α] [Ring α] (x y z : α) : (x - y) * z ~= x * z - y * z := by
  cnsimp [sub_eq_add_neg, add_mul]

class Semifield (α : Type u) [Eqv α] extends CommSemiring α, GroupWithZero α

class Field (α : Type u) [Eqv α] extends Semifield α, CommRing α

@[cnsimp]
theorem inv_neg [Eqv α] [Field α] {x : α} : (-x)⁻¹ ~= -x⁻¹ := by
  by_cases' h : x ~= 0
  · cnsimp [h]
  apply inv_eq_of_mul_eq_one
  cnsimp [mul_inv_cancel h]
