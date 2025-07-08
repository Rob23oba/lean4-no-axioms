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

--attribute [cnsimp] ge_iff_le
--attribute [cnsimp] gt_iff_lt

theorem le_of_eq [Eqv α] [Preorder α] {x y : α} (h : x ~= y) : x ≤ y :=
  Preorder.le_of_eq x y h

theorem le_trans [Eqv α] [Preorder α] {x y z : α} (h : x ≤ y) (h' : y ≤ z) : x ≤ z :=
  Preorder.le_trans x y z h h'

@[refl] theorem le_refl [Eqv α] [Preorder α] (x : α) : x ≤ x := le_of_eq .rfl
theorem le_rfl [Eqv α] [Preorder α] {x : α} : x ≤ x := le_refl x

@[cnsimp]
theorem le_self_iff [Eqv α] [Preorder α] {x : α} : x ≤ x ↔ True := iff_true_intro le_rfl

instance [Eqv α] [Preorder α] : LECongr α where
  le_congr h h' :=
    ⟨fun h'' => le_trans (le_of_eq h.symm) (le_trans h'' (le_of_eq h')),
      fun h'' => le_trans (le_of_eq h) (le_trans h'' (le_of_eq h'.symm))⟩

instance [Eqv α] [Preorder α] : LTCongr α where
  lt_congr h h' := by
    cnsimp only [Preorder.lt_iff_le_not_le]
    ccongr <;> assumption

theorem lt_of_le_of_lt [Eqv α] [Preorder α] {x y z : α} (h : x ≤ y) (h' : y < z) : x < z := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h' ⊢
  constructor
  · exact le_trans h h'.1
  · intro h''
    apply h'.2
    exact le_trans h'' h

theorem lt_of_lt_of_le [Eqv α] [Preorder α] {x y z : α} (h : x < y) (h' : y ≤ z) : x < z := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact le_trans h.1 h'
  · intro h''
    apply h.2
    exact le_trans h' h''

theorem le_of_lt [Eqv α] [Preorder α] {x y : α} (h : x < y) : x ≤ y := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h
  exact h.1

theorem lt_trans [Eqv α] [Preorder α] {x y z : α} (h : x < y) (h' : y < z) : x < z :=
  lt_of_le_of_lt (le_of_lt h) h'

theorem not_le_of_lt [Eqv α] [Preorder α] {x y : α} (h : x < y) : ¬y ≤ x := by
  cnsimp only [Preorder.lt_iff_le_not_le] at h
  exact h.2

theorem not_lt_of_le [Eqv α] [Preorder α] {x y : α} (h : x ≤ y) : ¬y < x := by
  cnsimp only [Preorder.lt_iff_le_not_le, not_and, not_not, h, imp_true_iff]

theorem lt_irrefl [Eqv α] [Preorder α] (x : α) : ¬x < x := by
  cnsimp only [Preorder.lt_iff_le_not_le, le_refl x, not_true, and_false_iff, not_false_iff]

@[cnsimp]
theorem lt_self_iff [Eqv α] [Preorder α] (x : α) : x < x ↔ False :=
  iff_false_intro (lt_irrefl x)

theorem lt_asymm [Eqv α] [Preorder α] {x y : α} (h : x < y) : ¬y < x :=
  not_lt_of_le (le_of_lt h)

theorem lt_of_eq'_of_lt [Eqv α] [LT α] [LTCongr α] {x y z : α} (h : x ~= y) (h' : y < z) : x < z := by
  cnsimp only [h, h']

theorem lt_of_lt_of_eq' [Eqv α] [LT α] [LTCongr α] {x y z : α} (h : x < y) (h' : y ~= z) : x < z := by
  cnsimp only [h, ← h']

theorem le_of_eq'_of_le [Eqv α] [LE α] [LECongr α] {x y z : α} (h : x ~= y) (h' : y ≤ z) : x ≤ z := by
  cnsimp only [h, h']

theorem le_of_le_of_eq' [Eqv α] [LE α] [LECongr α] {x y z : α} (h : x ≤ y) (h' : y ~= z) : x ≤ z := by
  cnsimp only [h, ← h']

theorem gt_of_eq'_of_gt [Eqv α] [LT α] [LTCongr α] {x y z : α} (h : x ~= y) (h' : y > z) : x > z := by
  cnsimp only [h, h']

theorem gt_of_gt_of_eq' [Eqv α] [LT α] [LTCongr α] {x y z : α} (h : x > y) (h' : y ~= z) : x > z := by
  cnsimp only [h, ← h']

theorem ge_of_eq'_of_ge [Eqv α] [LE α] [LECongr α] {x y z : α} (h : x ~= y) (h' : y ≥ z) : x ≥ z := by
  cnsimp only [h, h']

theorem ge_of_ge_of_eq' [Eqv α] [LE α] [LECongr α] {x y z : α} (h : x ≥ y) (h' : y ~= z) : x ≥ z := by
  cnsimp only [h, ← h']

theorem ge_trans [Eqv α] [Preorder α] {x y z : α} (h : x ≥ y) (h' : y ≥ z) : x ≥ z :=
  le_trans h' h

theorem gt_trans [Eqv α] [Preorder α] {x y z : α} (h : x > y) (h' : y > z) : x > z :=
  lt_trans h' h

theorem ge_of_eq [Eqv α] [Preorder α] {x y : α} (h : x ~= y) : x ≥ y :=
  le_of_eq h.symm

@[refl] theorem ge_refl [Eqv α] [Preorder α] (x : α) : x ≥ x :=
  le_refl x

theorem ge_rfl [Eqv α] [Preorder α] {x : α} : x ≥ x :=
  le_refl x

theorem gt_of_ge_of_gt [Eqv α] [Preorder α] {x y z : α} (h : x ≥ y) (h' : y > z) : x > z :=
  lt_of_lt_of_le h' h

theorem gt_of_gt_of_ge [Eqv α] [Preorder α] {x y z : α} (h : x > y) (h' : y ≥ z) : x > z :=
  lt_of_le_of_lt h' h

theorem gt_irrefl [Eqv α] [Preorder α] {x : α} : ¬x > x :=
  lt_irrefl x

theorem gt_asymm [Eqv α] [Preorder α] {x y : α} (h : x > y) : ¬y > x :=
  lt_asymm h

theorem not_lt_of_ge [Eqv α] [Preorder α] {x y : α} (h : x ≥ y) : ¬x < y :=
  not_lt_of_le h

theorem not_le_of_gt [Eqv α] [Preorder α] {x y : α} (h : x > y) : ¬x ≤ y :=
  not_le_of_lt h

theorem not_gt_of_le [Eqv α] [Preorder α] {x y : α} (h : x ≤ y) : ¬x > y :=
  not_lt_of_le h

theorem not_ge_of_lt [Eqv α] [Preorder α] {x y : α} (h : x < y) : ¬x ≥ y :=
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
abbrev LE.le.not_lt := @not_lt_of_le
abbrev GE.ge.not_lt := @not_lt_of_ge
abbrev LT.lt.not_le := @not_le_of_lt
abbrev GT.gt.not_le := @not_le_of_gt

class PartialOrder (α : Type u) [Eqv α] extends Preorder α where
  le_antisymm (x y : α) (h : x ≤ y) (h' : y ≤ x) : x ~= y

theorem le_antisymm [Eqv α] [PartialOrder α] {x y : α} (h : x ≤ y) (h' : y ≤ x) : x ~= y :=
  PartialOrder.le_antisymm x y h h'

class LinearOrder (α : Type u) [Eqv α] extends PartialOrder α where
  le_of_not_le (x y : α) : ¬x ≤ y → y ≤ x

theorem le_of_not_le [Eqv α] [LinearOrder α] {x y : α} (h : ¬x ≤ y) : y ≤ x := LinearOrder.le_of_not_le x y h

theorem le_total [Eqv α] [LinearOrder α] (x y : α) : x ≤ y ∨' y ≤ x := by
  by_contra' h
  cnsimp only [not_or'] at h
  exact absurd (le_of_not_le h.1) h.2

@[cnsimp]
theorem not_le [Eqv α] [LinearOrder α] {x y : α} : ¬x ≤ y ↔ y < x := by
  cnsimp only [Preorder.lt_iff_le_not_le]
  constructor
  · intro h
    exact ⟨le_of_not_le h, h⟩
  · intro ⟨_, h⟩
    exact h

@[cnsimp]
theorem not_lt [Eqv α] [LinearOrder α] {x y : α} : ¬x < y ↔ y ≤ x := by
  cnsimp only [← not_le, not_not, iff_self_iff_true]

theorem le_of_not_lt [Eqv α] [LinearOrder α] {x y : α} (h : ¬x < y) : y ≤ x := not_lt.mp h
theorem lt_of_not_le [Eqv α] [LinearOrder α] {x y : α} (h : ¬x ≤ y) : y < x := not_le.mp h

theorem le_iff_lt_or_eq [Eqv α] [LinearOrder α] {x y : α} : x ≤ y ↔ x < y ∨' x ~= y := by
  constructor
  · intro h
    by_contra' h'
    cnsimp only [not_or', not_lt] at h'
    exact absurd (le_antisymm h h'.1) h'.2
  · intro h
    exact h.elim le_of_lt le_of_eq

theorem lt_of_le_of_ne [Eqv α] [LinearOrder α] {x y : α} (h : x ≤ y) (h' : x ~!= y) : x < y := by
  cnsimp [le_iff_lt_or_eq] at h
  cnsimpa [show ¬_ from h'] using h

theorem lt_of_le_of_ne' [Eqv α] [LinearOrder α] {x y : α} (h : x ≤ y) (h' : y ~!= x) : x < y :=
  lt_of_le_of_ne h h'.symm

class IsStrictOrderedRing (α : Type u) [Eqv α] [Semiring α] [LinearOrder α] where
  le_of_add_le_add_right (x y z : α) : x + z ≤ y + z → x ≤ y
  le_of_mul_le_mul_right (x y z : α) (hz : 0 < z) : x * z ≤ y * z → x ≤ y

theorem le_of_add_le_add_right [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (h : x + z ≤ y + z) : x ≤ y :=
  IsStrictOrderedRing.le_of_add_le_add_right x y z h

theorem le_of_mul_le_mul_right [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (hz : 0 < z) (h : x * z ≤ y * z) : x ≤ y :=
  IsStrictOrderedRing.le_of_mul_le_mul_right x y z hz h

theorem add_le_add_right_of_le [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (h : x ≤ y) : x + z ≤ y + z := by
  apply le_of_not_lt
  intro h'
  cnsimp only [Preorder.lt_iff_le_not_le] at h'
  have h'' := le_of_add_le_add_right h'.1
  replace h'' := le_antisymm h h''
  cnsimp [h''] at h'

theorem mul_le_mul_right_of_le [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (hz : 0 ≤ z) (h : x ≤ y) : x * z ≤ y * z := by
  cnsimp only [le_iff_lt_or_eq] at hz
  apply hz.elim (fun hz => ?_) (fun hz => ?_)
  · apply le_of_not_lt
    intro h'
    cnsimp only [Preorder.lt_iff_le_not_le] at h'
    have h'' := le_of_mul_le_mul_right hz h'.1
    replace h'' := le_antisymm h h''
    cnsimp [h''] at h'
  · cnsimp [← hz]

@[cnsimp]
theorem add_le_add_iff_right [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} : x + z ≤ y + z ↔ x ≤ y :=
  ⟨le_of_add_le_add_right, add_le_add_right_of_le⟩

theorem le_of_add_le_add_left [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (h : x + y ≤ x + z) : y ≤ z := by
  cnrw [add_comm] at h
  exact le_of_add_le_add_right h

theorem add_le_add_left_of_le [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} (h : y ≤ z) : x + y ≤ x + z := by
  cnrw [add_comm]
  exact add_le_add_right_of_le h

@[cnsimp]
theorem add_le_add_iff_left [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y z : α} : x + y ≤ x + z ↔ y ≤ z :=
  ⟨le_of_add_le_add_left, add_le_add_left_of_le⟩
