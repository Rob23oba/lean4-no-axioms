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

class Inv (α : Type u) [Eqv α] where
  inv : α → α
  inv_congr : ∀ {x y}, x ~= y → inv x ~= inv y

postfix:max "⁻¹" => Inv.inv

/-- A type with a one element. -/
class One (α : Type u) where
  one : α

instance One.toOfNat1 [One α] : OfNat α 1 := ⟨One.one⟩
instance One.ofOfNat1 [OfNat α 1] : One α := ⟨1⟩

class LECongr (α : Type u) [Eqv α] [LE α] where
  le_congr {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂

@[ccongr]
theorem LECongr.ge_congr {α : Type u} {_ : Eqv α} {_ : LE α} [LECongr α]
    {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ≥ y₁ ↔ x₂ ≥ y₂ :=
  LECongr.le_congr hy hx

class LTCongr (α : Type u) [Eqv α] [LT α] where
  lt_congr {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ < y₁ ↔ x₂ < y₂

@[ccongr]
theorem LTCongr.gt_congr {α : Type u} {_ : Eqv α} {_ : LT α} [LTCongr α]
    {x₁ x₂ y₁ y₂ : α} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ > y₁ ↔ x₂ > y₂ :=
  LTCongr.lt_congr hy hx

export HAddCongr (add_congr)
export HSubCongr (sub_congr)
export HMulCongr (mul_congr)
export HDivCongr (div_congr)
export NegCongr (neg_congr)
export Inv (inv_congr)
export LECongr (le_congr ge_congr)
export LTCongr (lt_congr gt_congr)

attribute [ccongr] add_congr sub_congr mul_congr div_congr
  neg_congr inv_congr le_congr lt_congr

instance : AddCongr Nat where
  add_congr h h' := h ▸ h' ▸ rfl

instance : SubCongr Nat where
  sub_congr h h' := h ▸ h' ▸ rfl

instance : MulCongr Nat where
  mul_congr h h' := h ▸ h' ▸ rfl

instance : DivCongr Nat where
  div_congr h h' := h ▸ h' ▸ rfl

instance : LECongr Nat where
  le_congr h h' := h ▸ h' ▸ .rfl

instance : LTCongr Nat where
  lt_congr h h' := h ▸ h' ▸ .rfl

instance : AddCongr Int where
  add_congr h h' := h ▸ h' ▸ rfl

instance : SubCongr Int where
  sub_congr h h' := h ▸ h' ▸ rfl

instance : MulCongr Int where
  mul_congr h h' := h ▸ h' ▸ rfl

instance : DivCongr Int where
  div_congr h h' := h ▸ h' ▸ rfl

instance : LECongr Int where
  le_congr h h' := h ▸ h' ▸ .rfl

instance : LTCongr Int where
  lt_congr h h' := h ▸ h' ▸ .rfl

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
theorem mul_one {_ : Eqv α} [Monoid α] (x : α) : x * 1 ~= x := Monoid.mul_one x

@[cnsimp]
theorem add_zero {_ : Eqv α} [AddMonoid α] (x : α) : x + 0 ~= x := AddMonoid.add_zero x

@[cnsimp]
theorem one_mul {_ : Eqv α} [Monoid α] (x : α) : 1 * x ~= x := Monoid.one_mul x

@[cnsimp]
theorem zero_add {_ : Eqv α} [AddMonoid α] (x : α) : 0 + x ~= x := AddMonoid.zero_add x

theorem mul_assoc {_ : Eqv α} [Monoid α] (x y z : α) : x * y * z ~= x * (y * z) :=
  Monoid.mul_assoc x y z

theorem add_assoc {_ : Eqv α} [AddMonoid α] (x y z : α) : x + y + z ~= x + (y + z) :=
  AddMonoid.add_assoc x y z

class DivInvMonoid (α : Type u) [Eqv α] extends Monoid α, Inv α, Div α, DivCongr α where
  div_eq_mul_inv (x y : α) : x / y ~= x * y⁻¹

class SubNegMonoid (α : Type u) [Eqv α] extends AddMonoid α, Neg α, NegCongr α, Sub α, SubCongr α where
  sub_eq_add_neg (x y : α) : x - y ~= x + -y

theorem div_eq_mul_inv {_ : Eqv α} [DivInvMonoid α] (x y : α) : x / y ~= x * y⁻¹ :=
  DivInvMonoid.div_eq_mul_inv x y

theorem sub_eq_add_neg {_ : Eqv α} [SubNegMonoid α] (x y : α) : x - y ~= x + -y :=
  SubNegMonoid.sub_eq_add_neg x y

class MonoidWithZero (α : Type u) [Eqv α] extends Monoid α, Zero α where
  mul_zero (x : α) : x * 0 ~= 0
  zero_mul (x : α) : 0 * x ~= 0

@[cnsimp]
theorem mul_zero {_ : Eqv α} [MonoidWithZero α] (x : α) : x * 0 ~= 0 :=
  MonoidWithZero.mul_zero x

@[cnsimp]
theorem zero_mul {_ : Eqv α} [MonoidWithZero α] (x : α) : 0 * x ~= 0 :=
  MonoidWithZero.zero_mul x

class GroupWithZero (α : Type u) [Eqv α] extends MonoidWithZero α, DivInvMonoid α, Nontrivial α where
  inv_zero : (0 : α)⁻¹ ~= 0
  inv_mul_cancel (x : α) (h : x ~!= 0) : x⁻¹ * x ~= 1

class AddGroup (α : Type u) [Eqv α] extends SubNegMonoid α where
  neg_add_cancel (x : α) : -x + x ~= 0

theorem inv_mul_cancel {_ : Eqv α} [GroupWithZero α] {x : α} (h : x ~!= 0) : x⁻¹ * x ~= 1 :=
  GroupWithZero.inv_mul_cancel x h

@[cnsimp]
theorem neg_add_cancel {_ : Eqv α} [AddGroup α] (x : α) : -x + x ~= 0 := AddGroup.neg_add_cancel x

@[cnsimp]
theorem inv_zero {_ : Eqv α} [GroupWithZero α] : (0 : α)⁻¹ ~= 0 :=
  GroupWithZero.inv_zero

theorem inv_eq_zero_iff {_ : Eqv α} [GroupWithZero α] {x : α} : x⁻¹ ~= 0 ↔ x ~= 0 := by
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
theorem inv_inv {_ : Eqv α} [GroupWithZero α] (x : α) : x⁻¹⁻¹ ~= x := by
  by_cases' h : x ~= 0
  · cnsimp [h]
  calc
    x⁻¹⁻¹ ~= x⁻¹⁻¹ * (x⁻¹ * x) := by cnsimp only [inv_mul_cancel h, mul_one, eq'_self_iff]
    _ ~= (x⁻¹⁻¹ * x⁻¹) * x := by cnsimp only [mul_assoc, eq'_self_iff]
    _ ~= x := by cnsimp only [inv_mul_cancel (inv_eq_zero_iff.not.mpr h), one_mul, eq'_self_iff]

@[cnsimp]
theorem neg_neg {_ : Eqv α} [AddGroup α] (x : α) : -(-x) ~= x := by
  calc
    -(-x) ~= -(-x) + (-x + x) := by cnsimp only [neg_add_cancel, add_zero, eq'_self_iff]
    _ ~= (-(-x) + -x) + x := by cnsimp only [add_assoc, eq'_self_iff]
    _ ~= x := by cnsimp only [neg_add_cancel, zero_add, eq'_self_iff]

theorem mul_inv_cancel {_ : Eqv α} [GroupWithZero α] {x : α} (h : x ~!= 0) : x * x⁻¹ ~= 1 := by
  calc
    x * x⁻¹ ~= x⁻¹⁻¹ * x⁻¹ := by cnsimp only [inv_inv, eq'_self_iff]
    _ ~= 1 := by cnsimp only [inv_mul_cancel (inv_eq_zero_iff.not.mpr h), eq'_self_iff]

@[cnsimp]
theorem add_neg_cancel {_ : Eqv α} [AddGroup α] (x : α) : x + -x ~= 0 := by
  calc
    x + -x ~= -(-x) + -x := by cnsimp only [neg_neg, eq'_self_iff]
    _ ~= 0 := by cnsimp only [neg_add_cancel, eq'_self_iff]

theorem zero_ne_one {_ : Eqv α} [GroupWithZero α] : (0 : α) ~!= 1 := by
  intro h
  have : ∃' x y : α, x ~!= y := Nontrivial.exists_pair_ne
  refine this.elim fun a ha => ha.elim fun b hb => ?_
  apply hb
  calc
    a ~= a * 1 := by cnsimp
    _ ~= 0 := by cnsimp only [← h, mul_zero, eq'_self_iff]
    _ ~= b * 1 := by cnsimp only [← h, mul_zero, eq'_self_iff]
    _ ~= b := by cnsimp

theorem div_self {_ : Eqv α} [GroupWithZero α] {x : α} (h : x ~!= 0) : x / x ~= 1 := by
  cnsimp only [div_eq_mul_inv, mul_inv_cancel h, eq'_self_iff]

@[cnsimp]
theorem sub_self {_ : Eqv α} [AddGroup α] (x : α) : x - x ~= 0 := by
  cnsimp only [sub_eq_add_neg, add_neg_cancel, eq'_self_iff]

theorem mul_div_cancel_right {_ : Eqv α} [GroupWithZero α] {x y : α} (h : y ~!= 0) :
    x * y / y ~= x := by
  cnsimp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel h, mul_one, eq'_self_iff]

@[cnsimp]
theorem add_sub_cancel_right {_ : Eqv α} [AddGroup α] (x y : α) : x + y - y ~= x := by
  cnsimp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero, eq'_self_iff]

theorem div_mul_cancel {_ : Eqv α} [GroupWithZero α] {x y : α} (h : y ~!= 0) :
    x / y * y ~= x := by
  cnsimp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel h, mul_one, eq'_self_iff]

@[cnsimp]
theorem sub_add_cancel {_ : Eqv α} [AddGroup α] (x y : α) : x - y + y ~= x := by
  cnsimp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, eq'_self_iff]

theorem div_mul_assoc {_ : Eqv α} [DivInvMonoid α] (x y z : α) : x * y / z ~= x * (y / z) := by
  cnsimp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, eq'_self_iff]

theorem add_sub_assoc {_ : Eqv α} [AddGroup α] (x y z : α) : x + y - z ~= x + (y - z) := by
  cnsimp only [sub_eq_add_neg, add_assoc, eq'_self_iff]

@[cnsimp]
theorem inv_one {_ : Eqv α} [GroupWithZero α] : (1 : α)⁻¹ ~= 1 := by
  calc
    (1 : α)⁻¹ ~= 1⁻¹ * 1 := (mul_one _).symm
    _ ~= 1 := inv_mul_cancel zero_ne_one.symm

@[cnsimp]
theorem neg_zero {_ : Eqv α} [AddGroup α] : -(0 : α) ~= 0 := by
  calc
    -(0 : α) ~= -0 + 0 := (add_zero _).symm
    _ ~= 0 := neg_add_cancel 0

@[cnsimp]
theorem div_one {_ : Eqv α} [GroupWithZero α] (x : α) : x / 1 ~= x := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem sub_zero {_ : Eqv α} [AddGroup α] (x : α) : x - 0 ~= x := by
  cnsimp [sub_eq_add_neg]

@[cnsimp]
theorem div_zero {_ : Eqv α} [GroupWithZero α] (x : α) : x / 0 ~= 0 := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem zero_div {_ : Eqv α} [GroupWithZero α] (x : α) : 0 / x ~= 0 := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem one_div {_ : Eqv α} [GroupWithZero α] (x : α) : 1 / x ~= x⁻¹ := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem zero_sub {_ : Eqv α} [AddGroup α] (x : α) : 0 - x ~= -x := by
  cnsimp [sub_eq_add_neg]

theorem mul_ne_zero {_ : Eqv α} [GroupWithZero α] {x y : α}
    (h : x ~!= 0) (h' : y ~!= 0) : x * y ~!= 0 := by
  intro h''
  apply h
  calc
    x ~= x * (y * y⁻¹) := by cnsimp [mul_inv_cancel h']
    _ ~= x * y * y⁻¹ := by cnsimp [mul_assoc]
    _ ~= 0 := by cnsimp [h'']

@[cnsimp]
theorem mul_eq_zero {_ : Eqv α} [GroupWithZero α] {x y : α} : x * y ~= 0 ↔ x ~= 0 ∨' y ~= 0 := by
  constructor
  · intro h
    by_contra' h'
    cnsimp at h'
    exact mul_ne_zero h'.1 h'.2 h
  · intro h
    refine h.elim (fun h => ?_) (fun h => ?_) <;> cnsimp [h]

@[cnsimp]
theorem zero_eq_mul {_ : Eqv α} [GroupWithZero α] {x y : α} : 0 ~= x * y ↔ x ~= 0 ∨' y ~= 0 := by
  cnsimp [eq'_comm (x := (0 : α))]

@[cnsimp]
theorem inv_mul_rev {_ : Eqv α} [GroupWithZero α] (x y : α) : (x * y)⁻¹ ~= y⁻¹ * x⁻¹ := by
  by_cases' h : x ~= 0
  · cnsimp [h]
  by_cases' h' : y ~= 0
  · cnsimp [h']
  calc
    (x * y)⁻¹ ~= (x * y)⁻¹ * (x * (y * y⁻¹) * x⁻¹) := by cnsimp [mul_inv_cancel h, mul_inv_cancel h']
    _ ~= (x * y)⁻¹ * (x * y) * y⁻¹ * x⁻¹ := by cnsimp only [mul_assoc, eq'_self_iff]
    _ ~= y⁻¹ * x⁻¹ := by cnsimp [inv_mul_cancel (mul_ne_zero h h')]

@[cnsimp]
theorem neg_add_rev {_ : Eqv α} [AddGroup α] (x y : α) : -(x + y) ~= -y + -x := by
  calc
    -(x + y) ~= -(x + y) + (x + (y + -y) + -x) := by cnsimp
    _ ~= -(x + y) + (x + y) + -y + -x := by cnsimp only [add_assoc, eq'_self_iff]
    _ ~= -y + -x := by cnsimp

@[cnsimp]
theorem inv_div {_ : Eqv α} [GroupWithZero α] (x y : α) : (x / y)⁻¹ ~= y / x := by
  cnsimp [div_eq_mul_inv]

@[cnsimp]
theorem neg_sub {_ : Eqv α} [AddGroup α] (x y : α) : -(x - y) ~= y - x := by
  cnsimp [sub_eq_add_neg]

@[cnsimp]
theorem sub_neg {_ : Eqv α} [AddGroup α] (x y : α) : x - (-y) ~= x + y := by
  cnsimp [sub_eq_add_neg]

theorem mul_right_cancel {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (hz : z ~!= 0) (h : x * z ~= y * z) : x ~= y := by
  calc
    x ~= x * z / z := by cnsimp [mul_div_cancel_right hz]
    _ ~= y * z / z := by cnsimp [h]
    _ ~= y := by cnsimp [mul_div_cancel_right hz]

theorem add_right_cancel {_ : Eqv α} [AddGroup α] {x y z : α}
    (h : x + z ~= y + z) : x ~= y := by
  calc
    x ~= x + z - z := by cnsimp
    _ ~= y + z - z := by cnsimp only [h, eq'_self_iff]
    _ ~= y := by cnsimp

theorem mul_right_cancel_iff {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (h : z ~!= 0) : x * z ~= y * z ↔ x ~= y := by
  constructor
  · exact mul_right_cancel h
  · intro h
    cnsimp [h]

theorem add_right_cancel_iff {_ : Eqv α} [AddGroup α] {x y z : α} :
    x + z ~= y + z ↔ x ~= y := by
  constructor
  · exact add_right_cancel
  · intro h
    cnsimp [h]

theorem mul_left_cancel {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (hx : x ~!= 0) (h : x * y ~= x * z) : y ~= z := by
  calc
    y ~= x⁻¹ * x * y := by cnsimp [inv_mul_cancel hx]
    _ ~= x⁻¹ * x * z := by cnsimp [mul_assoc, h]
    _ ~= z := by cnsimp [inv_mul_cancel hx]

theorem add_left_cancel {_ : Eqv α} [AddGroup α] {x y z : α}
    (h : x + y ~= x + z) : y ~= z := by
  calc
    y ~= -x + x + y := by cnsimp
    _ ~= -x + x + z := by cnsimp only [add_assoc, h, eq'_self_iff]
    _ ~= z := by cnsimp

theorem mul_left_cancel_iff {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (h : x ~!= 0) : x * y ~= x * z ↔ y ~= z := by
  constructor
  · exact mul_left_cancel h
  · intro h
    cnsimp [h]

theorem add_left_cancel_iff {_ : Eqv α} [AddGroup α] {x y z : α} :
    x + y ~= x + z ↔ y ~= z := by
  constructor
  · exact add_left_cancel
  · intro h
    cnsimp [h]

theorem mul_right_inj {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (h : x ~!= 0) : x * y ~= x * z ↔ y ~= z :=
  mul_left_cancel_iff h

@[cnsimp]
theorem add_right_inj {_ : Eqv α} [AddGroup α] (x : α) {y z : α} :
    x + y ~= x + z ↔ y ~= z :=
  add_left_cancel_iff

theorem mul_left_inj {_ : Eqv α} [GroupWithZero α] {x y z : α}
    (h : z ~!= 0) : x * z ~= y * z ↔ x ~= y :=
  mul_right_cancel_iff h

@[cnsimp]
theorem add_left_inj {_ : Eqv α} [AddGroup α] {x y : α} (z : α) :
    x + z ~= y + z ↔ x ~= y :=
  add_right_cancel_iff

class CommMonoid (α : Type u) [Eqv α] extends Monoid α where
  mul_comm (x y : α) : x * y ~= y * x

class AddCommMonoid (α : Type u) [Eqv α] extends AddMonoid α where
  add_comm (x y : α) : x + y ~= y + x

theorem mul_comm {_ : Eqv α} [CommMonoid α] (x y : α) : x * y ~= y * x :=
  CommMonoid.mul_comm x y

theorem add_comm {_ : Eqv α} [AddCommMonoid α] (x y : α) : x + y ~= y + x :=
  AddCommMonoid.add_comm x y

theorem mul_right_comm {_ : Eqv α} [CommMonoid α] (x y z : α) : x * y * z ~= x * z * y := by
  cnsimp only [mul_assoc, mul_comm y, eq'_self_iff]

theorem add_right_comm {_ : Eqv α} [AddCommMonoid α] (x y z : α) : x + y + z ~= x + z + y := by
  cnsimp only [add_assoc, add_comm y, eq'_self_iff]

theorem mul_left_comm {_ : Eqv α} [CommMonoid α] (x y z : α) : x * (y * z) ~= y * (x * z) := by
  cnsimp only [← mul_assoc, mul_comm y, eq'_self_iff]

theorem add_left_comm {_ : Eqv α} [AddCommMonoid α] (x y z : α) : x + (y + z) ~= y + (x + z) := by
  cnsimp only [← add_assoc, add_comm y, eq'_self_iff]

class CommGroupWithZero (α : Type u) [Eqv α] extends GroupWithZero α, CommMonoid α

class AddCommGroup (α : Type u) [Eqv α] extends AddGroup α, AddCommMonoid α

theorem mul_div_cancel {_ : Eqv α} [CommGroupWithZero α] {x : α} (hx : x ~!= 0) (y : α) :
    x * (y / x) ~= y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y, ← mul_assoc, mul_inv_cancel hx]

@[cnsimp]
theorem add_sub_cancel {_ : Eqv α} [AddCommGroup α] (x y : α) : x + (y - x) ~= y := by
  cnsimp [sub_eq_add_neg, add_right_comm x y, ← add_assoc]

theorem mul_div_cancel_left {_ : Eqv α} [CommGroupWithZero α] {x : α} (hx : x ~!= 0) (y : α) :
    x * y / x ~= y := by
  cnsimp [mul_comm x, mul_div_cancel_right hx]

@[cnsimp]
theorem add_sub_cancel_left {_ : Eqv α} [AddCommGroup α] (x y : α) : x + y - x ~= y := by
  cnsimp [add_comm x]

theorem mul_div_comm {_ : Eqv α} [CommGroupWithZero α] (x y z : α) :
    x * y / z ~= x / z * y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y]

theorem add_sub_comm {_ : Eqv α} [AddCommGroup α] (x y z : α) :
    x + y - z ~= x - z + y := by
  cnsimp [sub_eq_add_neg, add_right_comm x y]

theorem div_right_comm {_ : Eqv α} [CommGroupWithZero α] (x y z : α) :
    x / y / z ~= x / z / y := by
  cnsimp [div_eq_mul_inv, mul_right_comm x y⁻¹]

theorem sub_right_comm {_ : Eqv α} [AddCommGroup α] (x y z : α) :
    x - y - z ~= x - z - y := by
  cnsimp [sub_eq_add_neg, add_right_comm x (-y)]

theorem div_div {_ : Eqv α} [CommGroupWithZero α] (x y z : α) :
    x / y / z ~= x / (y * z) := by
  cnsimp [div_eq_mul_inv, mul_assoc, mul_comm y⁻¹]

theorem sub_sub {_ : Eqv α} [AddCommGroup α] (x y z : α) :
    x - y - z ~= x - (y + z) := by
  cnsimp [sub_eq_add_neg, add_assoc, add_comm (-y)]

class AddMonoidWithOne (α : Type u) [Eqv α] extends NatCast α, AddMonoid α, One α where
  natCast_zero : natCast 0 ~= 0
  natCast_succ (n : Nat) : natCast (n + 1) ~= natCast n + 1

instance : AddMonoidWithOne Nat where
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_assoc := Nat.add_assoc
  natCast_zero := rfl
  natCast_succ _ := rfl

@[cnsimp]
theorem Nat.cast_zero {_ : Eqv α} [AddMonoidWithOne α] : ((0 : Nat) : α) ~= 0 :=
  AddMonoidWithOne.natCast_zero

theorem Nat.cast_succ {_ : Eqv α} [AddMonoidWithOne α] (n : Nat) :
    ((n + 1 : Nat) : α) ~= (n : α) + 1 :=
  AddMonoidWithOne.natCast_succ n

@[cnsimp]
theorem Nat.cast_one {_ : Eqv α} [AddMonoidWithOne α] :
    ((1 : Nat) : α) ~= 1 := by
  cnsimp [Nat.cast_succ, Nat.cast_zero]

@[cnsimp]
theorem Nat.cast_add {_ : Eqv α} [AddMonoidWithOne α] (x y : Nat) :
    ((x + y : Nat) : α) ~= (x + y : α) := by
  induction y with
  | zero => cnsimp
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
theorem Nat.cast_ofNat {_ : Eqv α} [AddMonoidWithOne α] (n : Nat) [Nat.AtLeastTwo n] :
    (no_index (OfNat.ofNat n : Nat) : α) ~= no_index (OfNat.ofNat n) := by
  rfl

class Semiring (α : Type u) [Eqv α] extends MonoidWithZero α, AddCommMonoid α, AddMonoidWithOne α where
  mul_add (x y z : α) : x * (y + z) ~= x * y + x * z
  add_mul (x y z : α) : (x + y) * z ~= x * z + y * z

theorem Nat.mul_assoc' (a b c : Nat) : a * b * c = a * (b * c) := by
  induction b with
  | zero => rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.succ_mul, Nat.mul_comm, Nat.mul_add, Nat.mul_comm, ih,
      Nat.mul_add, Nat.mul_comm a c]

instance : Semiring Nat where
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_assoc := Nat.mul_assoc'
  mul_zero := Nat.mul_zero
  zero_mul := Nat.zero_mul
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  natCast_zero := rfl
  natCast_succ _ := rfl
  mul_add := Nat.mul_add
  add_mul x y z := by rw [Nat.mul_comm _ z, Nat.mul_comm _ z, Nat.mul_comm _ z, Nat.mul_add]

class Ring (α : Type u) [Eqv α] extends AddCommGroup α, Semiring α

class CommRing (α : Type u) [Eqv α] extends Ring α, CommMonoid α

theorem mul_add {_ : Eqv α} [Semiring α] (x y z : α) : x * (y + z) ~= x * y + x * z :=
  Semiring.mul_add x y z

theorem add_mul {_ : Eqv α} [Semiring α] (x y z : α) : (x + y) * z ~= x * z + y * z :=
  Semiring.add_mul x y z

@[cnsimp]
theorem neg_mul {_ : Eqv α} [Ring α] (x y : α) : -x * y ~= -(x * y) := by
  apply add_left_cancel (x := x * y)
  cnsimp [← add_mul]

@[cnsimp]
theorem mul_neg {_ : Eqv α} [Ring α] (x y : α) : x * -y ~= -(x * y) := by
  apply add_left_cancel (x := x * y)
  cnsimp [← mul_add]

theorem mul_sub {_ : Eqv α} [Ring α] (x y z : α) : x * (y - z) ~= x * y - x * z := by
  cnsimp [sub_eq_add_neg, mul_add]

theorem sub_mul {_ : Eqv α} [Ring α] (x y z : α) : (x - y) * z ~= x * z - y * z := by
  cnsimp [sub_eq_add_neg, add_mul]
