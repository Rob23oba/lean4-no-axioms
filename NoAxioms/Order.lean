import NoAxioms.Ring

class Preorder (α : Type u) [Eqv α] extends LE α, LT α where
  [dne_le : ∀ x y : α, DNE (x ≤ y)]
  le_of_eq (x y : α) (h : x ~= y) : x ≤ y
  le_trans (x y z : α) (h : x ≤ y) (h' : y ≤ z) : x ≤ z
  lt := fun a b : α => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

instance [Eqv α] [Preorder α] (x y : α) : DNE (x ≤ y) := Preorder.dne_le x y
instance [Eqv α] [Preorder α] (x y : α) : DNE (x < y) where
  dne h := by
    cnsimp only [Preorder.lt_iff_le_not_le] at h ⊢
    exact DNE.dne h

attribute [cnsimp] ge_iff_le
attribute [cnsimp] gt_iff_lt

theorem le_of_eq {_ : Eqv α} [Preorder α] {x y : α} (h : x ~= y) : x ≤ y :=
  Preorder.le_of_eq x y h

theorem le_trans {_ : Eqv α} [Preorder α] {x y z : α} (h : x ≤ y) (h' : y ≤ z) : x ≤ z :=
  Preorder.le_trans x y z h h'

@[refl] theorem le_refl {_ : Eqv α} [Preorder α] (x : α) : x ≤ x := le_of_eq .rfl
theorem le_rfl {_ : Eqv α} [Preorder α] {x : α} : x ≤ x := le_refl x

@[cnsimp]
theorem le_self_iff {_ : Eqv α} [Preorder α] {x : α} : x ≤ x ↔ True := iff_true_intro le_rfl

instance [Eqv α] [Preorder α] : LECongr α where
  le_congr h h' :=
    ⟨fun h'' => le_trans (le_of_eq h.symm) (le_trans h'' (le_of_eq h')),
      fun h'' => le_trans (le_of_eq h) (le_trans h'' (le_of_eq h'.symm))⟩

instance [Eqv α] [Preorder α] : LTCongr α where
  lt_congr h h' := by
    cnsimp only [Preorder.lt_iff_le_not_le]
    ccongr <;> assumption

theorem lt_of_le_of_lt {_ : Eqv α} [Preorder α] {x y z : α} (h : x ≤ y) (h' : y < z) : x < z := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h' ⊢
  constructor
  · exact le_trans h h'.1
  · intro h''
    apply h'.2
    exact le_trans h'' h

theorem lt_of_lt_of_le {_ : Eqv α} [Preorder α] {x y z : α} (h : x < y) (h' : y ≤ z) : x < z := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact le_trans h.1 h'
  · intro h''
    apply h.2
    exact le_trans h' h''

theorem le_of_lt {_ : Eqv α} [Preorder α] {x y : α} (h : x < y) : x ≤ y := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h
  exact h.1

theorem lt_trans {_ : Eqv α} [Preorder α] {x y z : α} (h : x < y) (h' : y < z) : x < z :=
  lt_of_le_of_lt (le_of_lt h) h'

theorem not_le_of_lt {_ : Eqv α} [Preorder α] {x y : α} (h : x < y) : ¬y ≤ x := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h
  exact h.2

theorem not_lt_of_le {_ : Eqv α} [Preorder α] {x y : α} (h : x ≤ y) : ¬y < x := by
  cnsimp only [Preorder.lt_iff_le_not_le, not_and, not_not, h, imp_true_iff]

theorem lt_irrefl {_ : Eqv α} [Preorder α] (x : α) : ¬x < x := by
  cnsimp only [Preorder.lt_iff_le_not_le, le_refl x, not_true, and_false_iff, not_false_iff]

@[cnsimp]
theorem lt_self_iff {_ : Eqv α} [Preorder α] (x : α) : x < x ↔ False :=
  iff_false_intro (lt_irrefl x)

theorem lt_asymm {_ : Eqv α} [Preorder α] {x y : α} (h : x < y) : ¬y < x :=
  not_lt_of_le (le_of_lt h)

theorem lt_of_eq'_of_lt {_ : Eqv α} [LT α] [LTCongr α] {x y z : α} (h : x ~= y) (h' : y < z) : x < z := by
  cnsimp only [h, h']

theorem lt_of_lt_of_eq' {_ : Eqv α} [LT α] [LTCongr α] {x y z : α} (h : x < y) (h' : y ~= z) : x < z := by
  cnsimp only [h, ← h']

theorem le_of_eq'_of_le {_ : Eqv α} [LE α] [LECongr α] {x y z : α} (h : x ~= y) (h' : y ≤ z) : x ≤ z := by
  cnsimp only [h, h']

theorem le_of_le_of_eq' {_ : Eqv α} [LE α] [LECongr α] {x y z : α} (h : x ≤ y) (h' : y ~= z) : x ≤ z := by
  cnsimp only [h, ← h']

theorem gt_of_eq'_of_gt {_ : Eqv α} [LT α] [LTCongr α] {x y z : α} (h : x ~= y) (h' : y > z) : x > z := by
  cnsimp only [h, h']

theorem gt_of_gt_of_eq' {_ : Eqv α} [LT α] [LTCongr α] {x y z : α} (h : x > y) (h' : y ~= z) : x > z := by
  cnsimp only [h, ← h']

theorem ge_of_eq'_of_ge {_ : Eqv α} [LE α] [LECongr α] {x y z : α} (h : x ~= y) (h' : y ≥ z) : x ≥ z := by
  cnsimp only [h, h']

theorem ge_of_ge_of_eq' {_ : Eqv α} [LE α] [LECongr α] {x y z : α} (h : x ≥ y) (h' : y ~= z) : x ≥ z := by
  cnsimp only [h, ← h']

theorem ge_trans {_ : Eqv α} [Preorder α] {x y z : α} (h : x ≥ y) (h' : y ≥ z) : x ≥ z :=
  le_trans h' h

theorem gt_trans {_ : Eqv α} [Preorder α] {x y z : α} (h : x > y) (h' : y > z) : x > z :=
  lt_trans h' h

theorem ge_of_eq {_ : Eqv α} [Preorder α] {x y : α} (h : x ~= y) : x ≥ y :=
  le_of_eq h.symm

@[refl] theorem ge_refl {_ : Eqv α} [Preorder α] (x : α) : x ≥ x :=
  le_refl x

theorem ge_rfl {_ : Eqv α} [Preorder α] {x : α} : x ≥ x :=
  le_refl x

theorem gt_of_ge_of_gt {_ : Eqv α} [Preorder α] {x y z : α} (h : x ≥ y) (h' : y > z) : x > z :=
  lt_of_lt_of_le h' h

theorem gt_of_gt_of_ge {_ : Eqv α} [Preorder α] {x y z : α} (h : x > y) (h' : y ≥ z) : x > z :=
  lt_of_le_of_lt h' h

theorem gt_irrefl {_ : Eqv α} [Preorder α] {x : α} : ¬x > x :=
  lt_irrefl x

theorem gt_asymm {_ : Eqv α} [Preorder α] {x y : α} (h : x > y) : ¬y > x :=
  lt_asymm h

theorem not_lt_of_ge {_ : Eqv α} [Preorder α] {x y : α} (h : x ≥ y) : ¬x < y :=
  not_lt_of_le h

theorem not_le_of_gt {_ : Eqv α} [Preorder α] {x y : α} (h : x > y) : ¬x ≤ y :=
  not_le_of_lt h

theorem not_gt_of_le {_ : Eqv α} [Preorder α] {x y : α} (h : x ≤ y) : ¬x > y :=
  not_lt_of_le h

theorem not_ge_of_lt {_ : Eqv α} [Preorder α] {x y : α} (h : x < y) : ¬x ≥ y :=
  not_le_of_lt h

instance [Eqv α] [LE α] [LECongr α] : @Trans α α α LE.le Eq' LE.le := ⟨le_of_le_of_eq'⟩
instance [Eqv α] [LE α] [LECongr α] : @Trans α α α Eq' LE.le LE.le := ⟨le_of_eq'_of_le⟩
instance [Eqv α] [LT α] [LTCongr α] : @Trans α α α LT.lt Eq' LT.lt := ⟨lt_of_lt_of_eq'⟩
instance [Eqv α] [LT α] [LTCongr α] : @Trans α α α Eq' LT.lt LT.lt := ⟨lt_of_eq'_of_lt⟩
instance [Eqv α] [LE α] [LECongr α] : @Trans α α α GE.ge Eq' GE.ge := ⟨ge_of_ge_of_eq'⟩
instance [Eqv α] [LE α] [LECongr α] : @Trans α α α Eq' GE.ge GE.ge := ⟨ge_of_eq'_of_ge⟩
instance [Eqv α] [LT α] [LTCongr α] : @Trans α α α GT.gt Eq' GT.gt := ⟨gt_of_gt_of_eq'⟩
instance [Eqv α] [LT α] [LTCongr α] : @Trans α α α Eq' GT.gt GT.gt := ⟨gt_of_eq'_of_gt⟩

instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α GE.ge GT.gt GT.gt := ⟨gt_of_ge_of_gt⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α GT.gt GE.ge GT.gt := ⟨gt_of_gt_of_ge⟩
instance (priority := 900) [Eqv α] [Preorder α] : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩

abbrev LE.le.refl := @le_refl
abbrev GE.ge.refl := @ge_refl
abbrev LE.le.rfl := @le_rfl
abbrev GE.ge.rfl := @ge_rfl
abbrev LE.le.trans := @le_trans
abbrev LT.lt.trans := @lt_trans
abbrev GE.ge.trans := @ge_trans
abbrev GT.gt.trans := @gt_trans

instance : Preorder Nat where
  le_of_eq _ _ h := Nat.le_of_eq h
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_le _ _ := Nat.lt_iff_le_not_le

class PartialOrder (α : Type u) [Eqv α] extends Preorder α where
  le_antisymm (x y : α) (h : x ≤ y) (h' : y ≤ x) : x ~= y

instance : PartialOrder Nat where
  le_antisymm _ _ := Nat.le_antisymm
