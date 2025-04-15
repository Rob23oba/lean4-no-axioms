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

attribute [ccongr] HAddCongr.add_congr
attribute [ccongr] HSubCongr.sub_congr
attribute [ccongr] HMulCongr.mul_congr
attribute [ccongr] HDivCongr.div_congr
attribute [ccongr] NegCongr.neg_congr
attribute [ccongr] Inv.inv_congr
attribute [ccongr] LECongr.le_congr
attribute [ccongr] LTCongr.lt_congr
