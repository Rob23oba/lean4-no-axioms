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

theorem ne_of_lt [Eqv α] [Preorder α] {x y : α} (h : x < y) : x ~!= y := by
  intro h'
  cnsimp [h'] at h

theorem ne_of_gt [Eqv α] [Preorder α] {x y : α} (h : y < x) : x ~!= y := by
  intro h'
  cnsimp [h'] at h

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
abbrev LT.lt.le := @le_of_lt
abbrev GT.gt.ge := @le_of_lt
abbrev LT.lt.ne := @ne_of_lt
abbrev LT.lt.ne' := @ne_of_gt
abbrev GT.gt.ne := @ne_of_gt
abbrev GT.gt.ne' := @ne_of_lt
abbrev LE.le.not_lt := @not_lt_of_le
abbrev LE.le.not_gt := @not_lt_of_le
abbrev GE.ge.not_lt := @not_lt_of_ge
abbrev GE.ge.not_gt := @not_lt_of_ge
abbrev LT.lt.not_lt := @lt_asymm
abbrev LT.lt.not_gt := @lt_asymm
abbrev GT.gt.not_lt := @lt_asymm
abbrev GT.gt.not_gt := @lt_asymm
abbrev LT.lt.not_le := @not_le_of_lt
abbrev LT.lt.not_ge := @not_le_of_lt
abbrev GT.gt.not_le := @not_le_of_gt
abbrev GT.gt.not_ge := @not_le_of_gt

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

class IsStrictOrderedRing (α : Type u) [Eqv α] [Semiring α] [LinearOrder α] extends Nontrivial α where
  le_of_add_le_add_right (x y z : α) : x + z ≤ y + z → x ≤ y
  le_of_mul_le_mul_left (x y z : α) (hx : 0 < x) : x * y ≤ x * z → y ≤ z
  le_of_mul_le_mul_right (x y z : α) (hz : 0 < z) : x * z ≤ y * z → x ≤ y
  zero_le_one : (0 : α) ≤ 1

section Semiring

variable {α : Type u} [Eqv α] [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_of_add_le_add_right {x y z : α} (h : x + z ≤ y + z) : x ≤ y :=
  IsStrictOrderedRing.le_of_add_le_add_right x y z h

theorem le_of_mul_le_mul_left {x y z : α} (h : x * y ≤ x * z) (hx : 0 < x) : y ≤ z :=
  IsStrictOrderedRing.le_of_mul_le_mul_left x y z hx h

theorem le_of_mul_le_mul_right {x y z : α} (h : x * z ≤ y * z) (hz : 0 < z) : x ≤ y :=
  IsStrictOrderedRing.le_of_mul_le_mul_right x y z hz h

theorem zero_le_one : (0 : α) ≤ 1 :=
  IsStrictOrderedRing.zero_le_one

theorem add_le_add_right {x y z : α} (h : x ≤ y) : x + z ≤ y + z := by
  apply le_of_not_lt
  intro h'
  cnsimp only [Preorder.lt_iff_le_not_le] at h'
  have h'' := le_of_add_le_add_right h'.1
  replace h'' := le_antisymm h h''
  cnsimp [h''] at h'

@[cnsimp]
theorem add_le_add_iff_right {x y z : α} : x + z ≤ y + z ↔ x ≤ y :=
  ⟨le_of_add_le_add_right, add_le_add_right⟩

theorem le_of_add_le_add_left {x y z : α} (h : x + y ≤ x + z) : y ≤ z := by
  cnrw [add_comm] at h
  exact le_of_add_le_add_right h

theorem add_le_add_left {x y z : α} (h : y ≤ z) : x + y ≤ x + z := by
  cnrw [add_comm]
  exact add_le_add_right h

@[cnsimp]
theorem add_le_add_iff_left {x y z : α} : x + y ≤ x + z ↔ y ≤ z :=
  ⟨le_of_add_le_add_left, add_le_add_left⟩

@[cnsimp]
theorem add_lt_add_iff_right {x y z : α} : x + z < y + z ↔ x < y := by
  cnsimp only [← not_le, add_le_add_iff_right, iff_self_iff_true]

@[cnsimp]
theorem add_lt_add_iff_left {x y z : α} : x + y < x + z ↔ y < z := by
  cnsimp only [← not_le, add_le_add_iff_left, iff_self_iff_true]

theorem lt_of_add_lt_add_right {x y z : α} (h : x + z < y + z) : x < y :=
  add_lt_add_iff_right.mp h

theorem add_lt_add_right {x y z : α} (h : x < y) : x + z < y + z :=
  add_lt_add_iff_right.mpr h

theorem lt_of_add_lt_add_left {x y z : α} (h : x + y < x + z) : y < z :=
  add_lt_add_iff_left.mp h

theorem add_lt_add_left {x y z : α} (h : y < z) : x + y < x + z :=
  add_lt_add_iff_left.mpr h

theorem add_lt_add {a b c d : α} (h : a < c) (h' : b ≤ d) : a + b < c + d :=
  trans (add_lt_add_right h) (add_le_add_left h')

theorem add_lt_add' {a b c d : α} (h : a ≤ c) (h' : b < d) : a + b < c + d :=
  trans (add_le_add_right h) (add_lt_add_left h')

theorem add_le_add {a b c d : α} (h : a ≤ c) (h' : b ≤ d) : a + b ≤ c + d :=
  trans (add_le_add_right h) (add_le_add_left h')

theorem add_pos {x y : α} (hx : 0 < x) (hy : 0 ≤ y) : 0 < x + y := by
  cnsimpa using add_lt_add hx hy

theorem add_pos' {x y : α} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  cnsimpa using add_lt_add' hx hy

theorem add_nonneg {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  cnsimpa using add_le_add hx hy

theorem lt_add_right_of_pos {x y : α} (hy : 0 < y) : x < x + y := by
  cnsimpa using add_lt_add_left (x := x) hy

theorem lt_add_left_of_pos {x y : α} (hx : 0 < x) : y < x + y := by
  cnsimpa using add_lt_add_right (z := y) hx

theorem add_lt_left_of_neg {x y : α} (hy : y < 0) : x + y < x := by
  cnsimpa using add_lt_add_left (x := x) hy

theorem add_lt_right_of_neg {x y : α} (hx : x < 0) : x + y < y := by
  cnsimpa using add_lt_add_right (z := y) hx

theorem le_add_right_of_nonneg {x y : α} (hy : 0 ≤ y) : x ≤ x + y := by
  cnsimpa using add_le_add_left (x := x) hy

theorem le_add_left_of_nonneg {x y : α} (hx : 0 ≤ x) : y ≤ x + y := by
  cnsimpa using add_le_add_right (z := y) hx

theorem add_le_left_of_nonpos {x y : α} (hy : y ≤ 0) : x + y ≤ x := by
  cnsimpa using add_le_add_left (x := x) hy

theorem add_le_right_of_nonpos {x y : α} (hx : x ≤ 0) : x + y ≤ y := by
  cnsimpa using add_le_add_right (z := y) hx

theorem mul_lt_mul_of_pos_left {x y z : α} (h : y < z) (hx : 0 < x) : x * y < x * z := by
  cnsimp only [← not_le] at h ⊢
  intro h'
  apply h
  exact le_of_mul_le_mul_left h' hx

theorem mul_lt_mul_of_pos_right {x y z : α} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  cnsimp only [← not_le] at h ⊢
  intro h'
  apply h
  exact le_of_mul_le_mul_right h' hz

theorem mul_le_mul_of_nonneg_left {x y z : α} (h : y ≤ z) (hx : 0 ≤ x)  : x * y ≤ x * z := by
  cnsimp only [le_iff_lt_or_eq] at h hx
  apply hx.elim (fun hx => ?_) (fun hx => ?_)
  · apply h.elim (fun h => ?_) (fun h => ?_)
    · exact le_of_lt (mul_lt_mul_of_pos_left h hx)
    · cnsimp [h]
  · cnsimp [← hx]

theorem mul_le_mul_of_nonneg_right {x y z : α} (h : x ≤ y) (hz : 0 ≤ z)  : x * z ≤ y * z := by
  cnsimp only [le_iff_lt_or_eq] at h hz
  apply hz.elim (fun hz => ?_) (fun hz => ?_)
  · apply h.elim (fun h => ?_) (fun h => ?_)
    · exact le_of_lt (mul_lt_mul_of_pos_right h hz)
    · cnsimp [h]
  · cnsimp [← hz]

theorem lt_of_mul_lt_mul_left {x y z : α} (h : x * y < x * z) (hx : 0 ≤ x) : y < z := by
  cnsimp only [← not_le] at h ⊢
  intro h'
  apply h
  exact mul_le_mul_of_nonneg_left h' hx

theorem lt_of_mul_lt_mul_right {x y z : α} (h : x * z < y * z) (hz : 0 ≤ z) : x < y := by
  cnsimp only [← not_le] at h ⊢
  intro h'
  apply h
  exact mul_le_mul_of_nonneg_right h' hz

theorem mul_lt_mul_iff_of_pos_left {x y z : α} (h : 0 < x) : x * y < x * z ↔ y < z :=
  ⟨(lt_of_mul_lt_mul_left · (le_of_lt h)), (mul_lt_mul_of_pos_left · h)⟩

theorem mul_le_mul_iff_of_pos_left {x y z : α} (h : 0 < x) : x * y ≤ x * z ↔ y ≤ z :=
  ⟨(le_of_mul_le_mul_left · h), (mul_le_mul_of_nonneg_left · (le_of_lt h))⟩

theorem mul_lt_mul_iff_of_pos_right {x y z : α} (h : 0 < z) : x * z < y * z ↔ x < y :=
  ⟨(lt_of_mul_lt_mul_right · (le_of_lt h)), (mul_lt_mul_of_pos_right · h)⟩

theorem mul_le_mul_iff_of_pos_right {x y z : α} (h : 0 < z) : x * z ≤ y * z ↔ x ≤ y :=
  ⟨(le_of_mul_le_mul_right · h), (mul_le_mul_of_nonneg_right · (le_of_lt h))⟩

theorem mul_lt_mul {a b c d : α} (h : a < c) (h' : b ≤ d) (hb : 0 < b) (hc : 0 ≤ c) : a * b < c * d :=
  trans (mul_lt_mul_of_pos_right h hb) (mul_le_mul_of_nonneg_left h' hc)

theorem mul_lt_mul' {a b c d : α} (h : a ≤ c) (h' : b < d) (hb : 0 ≤ b) (hc : 0 < c) : a * b < c * d :=
  trans (mul_le_mul_of_nonneg_right h hb) (mul_lt_mul_of_pos_left h' hc)

theorem mul_le_mul {a b c d : α} (h : a ≤ c) (h' : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b ≤ c * d :=
  trans (mul_le_mul_of_nonneg_right h hb) (mul_le_mul_of_nonneg_left h' hc)

theorem mul_le_mul_of_nonneg' {a b c d : α} (h : a ≤ c) (h' : b ≤ d) (hb : 0 ≤ a) (hd : 0 ≤ d) : a * b ≤ c * d :=
  trans (mul_le_mul_of_nonneg_left h' hb) (mul_le_mul_of_nonneg_right h hd)

theorem mul_pos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  cnrw [← zero_mul y]
  exact mul_lt_mul_of_pos_right hx hy

theorem mul_nonneg {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  cnrw [← zero_mul y]
  exact mul_le_mul_of_nonneg_right hx hy

theorem zero_lt_one [Nontrivial α] : (0 : α) < 1 := by
  by_contra' h
  cnsimp only [not_lt] at h
  replace h := le_antisymm h zero_le_one
  exact absurd h.symm zero_ne_one

end Semiring

section Ring

variable {α : Type u} [Eqv α] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

theorem neg_le_neg {x y : α} (h : x ≤ y) : -y ≤ -x := by
  apply le_of_add_le_add_left (x := y)
  cnsimp only [add_neg_cancel]
  apply le_of_add_le_add_left (x := x)
  cnsimp only [add_zero, add_left_comm x, add_neg_cancel]
  exact h

theorem neg_le_neg_iff {x y : α} : -y ≤ -x ↔ x ≤ y := by
  constructor
  · intro h
    calc
      x ~= -(-x) := by cnsimp
      _ ≤ -(-y) := neg_le_neg h
      _ ~= y := by cnsimp
  · exact neg_le_neg

theorem neg_lt_neg_iff {x y : α} : -y < -x ↔ x < y := by
  cnsimp only [← not_le, neg_le_neg_iff, iff_self_iff_true]

theorem neg_lt_neg {x y : α} (h : x < y) : -y < -x := neg_lt_neg_iff.mpr h

theorem neg_nonneg {x : α} : 0 ≤ -x ↔ x ≤ 0 := by
  calc
    _ ↔ x + 0 ≤ x + -x := add_le_add_iff_left.symm
    _ ↔ x ≤ 0 := by cnsimp

theorem neg_nonpos {x : α} : -x ≤ 0 ↔ 0 ≤ x := by
  calc
    _ ↔ x + -x ≤ x + 0 := add_le_add_iff_left.symm
    _ ↔ 0 ≤ x := by cnsimp

theorem neg_lt_zero_iff {x : α} : -x < 0 ↔ 0 < x := by
  cnsimp only [← not_le, neg_nonneg, iff_self_iff_true]

theorem neg_pos {x : α} : 0 < -x ↔ x < 0 := by
  cnsimp only [← not_le, neg_nonpos, iff_self_iff_true]

theorem neg_le_symm {x y : α} (h : -x ≤ y) : -y ≤ x := by
  calc
    -y ~= x + -x + -y := by cnsimp
    _ ≤ x + y + -y := add_le_add_right (add_le_add_left h)
    _ ~= x := by cnsimp [add_assoc]

theorem neg_le_comm (x y : α) : -x ≤ y ↔ -y ≤ x :=
  ⟨neg_le_symm, neg_le_symm⟩

theorem mul_le_mul_of_nonpos_right {x y z : α} (h : y ≤ x) (hz : z ≤ 0) : x * z ≤ y * z := by
  apply neg_le_neg_iff.mp
  cnsimp only [← mul_neg]
  exact mul_le_mul_of_nonneg_right h (neg_nonneg.mpr hz)

theorem mul_le_mul_of_nonpos_left {x y z : α} (h : z ≤ y) (hx : x ≤ 0) : x * y ≤ x * z := by
  apply neg_le_neg_iff.mp
  cnsimp only [← neg_mul]
  exact mul_le_mul_of_nonneg_left h (neg_nonneg.mpr hx)

theorem mul_lt_mul_of_neg_right {x y z : α} (h : y < x) (hz : z < 0) : x * z < y * z := by
  apply neg_lt_neg_iff.mp
  cnsimp only [← mul_neg]
  exact mul_lt_mul_of_pos_right h (neg_pos.mpr hz)

theorem mul_lt_mul_of_neg_left {x y z : α} (h : z < y) (hx : x < 0) : x * y < x * z := by
  apply neg_lt_neg_iff.mp
  cnsimp only [← neg_mul]
  exact mul_lt_mul_of_pos_left h (neg_pos.mpr hx)

theorem mul_nonneg_of_nonpos_of_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  cnsimpa using mul_le_mul_of_nonpos_right ha hb

theorem mul_nonpos_of_nonneg_of_nonpos {a b : α} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  cnsimpa using mul_le_mul_of_nonpos_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg {a b : α} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  cnsimpa using mul_le_mul_of_nonpos_left hb ha

theorem sub_le_iff_le_add {x y z : α} : x - y ≤ z ↔ x ≤ z + y := by
  calc
    _ ↔ x - y + y ≤ z + y := add_le_add_iff_right.symm
    _ ↔ _ := by cnsimp

theorem sub_le_iff_le_add' {x y z : α} : x - y ≤ z ↔ x ≤ y + z := by
  cnsimp [sub_le_iff_le_add, add_comm z]

theorem le_sub_iff_add_le {x y z : α} : x ≤ y - z ↔ x + z ≤ y := by
  calc
    _ ↔ x + z ≤ y - z + z := add_le_add_iff_right.symm
    _ ↔ _ := by cnsimp

theorem le_sub_iff_add_le' {x y z : α} : x ≤ y - z ↔ z + x ≤ y := by
  cnsimp [le_sub_iff_add_le, add_comm z]

theorem sub_lt_iff_lt_add {x y z : α} : x - y < z ↔ x < z + y := by
  calc
    _ ↔ x - y + y < z + y := add_lt_add_iff_right.symm
    _ ↔ _ := by cnsimp

theorem sub_lt_iff_lt_add' {x y z : α} : x - y < z ↔ x < y + z := by
  cnsimp [sub_lt_iff_lt_add, add_comm z]

theorem lt_sub_iff_add_lt {x y z : α} : x < y - z ↔ x + z < y := by
  calc
    _ ↔ x + z < y - z + z := add_lt_add_iff_right.symm
    _ ↔ _ := by cnsimp

theorem lt_sub_iff_add_lt' {x y z : α} : x < y - z ↔ z + x < y := by
  cnsimp [lt_sub_iff_add_lt, add_comm z]

theorem sub_lt_sub {a b c d : α} (h : a < c) (h' : d ≤ b) :
    a - b < c - d := by
  cnsimp only [lt_sub_iff_add_lt, ← add_sub_comm, sub_lt_iff_lt_add]
  exact add_lt_add h h'

theorem sub_lt_sub' {a b c d : α} (h : a ≤ c) (h' : d < b) :
    a - b < c - d := by
  cnsimp only [lt_sub_iff_add_lt, ← add_sub_comm, sub_lt_iff_lt_add]
  exact add_lt_add' h h'

theorem sub_lt_sub_right {a b c : α} (h : a < b) : a - c < b - c := by
  cnsimp [sub_eq_add_neg, h]

theorem sub_lt_sub_left {a b c : α} (h : c < b) : a - b < a - c := by
  cnsimpa [sub_eq_add_neg, neg_lt_neg_iff] using h

theorem sub_le_sub {a b c d : α} (h : a ≤ c) (h' : d ≤ b) :
    a - b ≤ c - d := by
  cnsimp only [le_sub_iff_add_le, ← add_sub_comm, sub_le_iff_le_add]
  exact add_le_add h h'

theorem sub_le_sub_right {a b c : α} (h : a ≤ b) : a - c ≤ b - c := by
  cnsimp [sub_eq_add_neg, h]

theorem sub_le_sub_left {a b c : α} (h : c ≤ b) : a - b ≤ a - c := by
  cnsimpa [sub_eq_add_neg, neg_le_neg_iff] using h

end Ring

section Semifield

variable {α : Type u} [Eqv α] [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

theorem div_le_iff {x y z : α} (h : 0 < y) : x / y ≤ z ↔ x ≤ z * y := by
  calc
    _ ↔ x / y * y ≤ z * y := (mul_le_mul_iff_of_pos_right h).symm
    _ ↔ _ := by cnsimp [div_mul_cancel h.ne']

theorem div_le_iff' {x y z : α} (h : 0 < y) : x / y ≤ z ↔ x ≤ y * z := by
  cnsimp only [div_le_iff h, mul_comm z, iff_self_iff_true]

theorem div_lt_iff {x y z : α} (h : 0 < y) : x / y < z ↔ x < z * y := by
  calc
    _ ↔ x / y * y < z * y := (mul_lt_mul_iff_of_pos_right h).symm
    _ ↔ _ := by cnsimp [div_mul_cancel h.ne']

theorem div_lt_iff' {x y z : α} (h : 0 < y) : x / y < z ↔ x < y * z := by
  cnsimp only [div_lt_iff h, mul_comm z, iff_self_iff_true]

theorem le_div_iff {x y z : α} (h : 0 < z) : x ≤ y / z ↔ x * z ≤ y := by
  calc
    _ ↔ x * z ≤ y / z * z := (mul_le_mul_iff_of_pos_right h).symm
    _ ↔ _ := by cnsimp [div_mul_cancel h.ne']

theorem le_div_iff' {x y z : α} (h : 0 < z) : x ≤ y / z ↔ z * x ≤ y := by
  cnsimp only [le_div_iff h, mul_comm x, iff_self_iff_true]

theorem lt_div_iff {x y z : α} (h : 0 < z) : x < y / z ↔ x * z < y := by
  calc
    _ ↔ x * z < y / z * z := (mul_lt_mul_iff_of_pos_right h).symm
    _ ↔ _ := by cnsimp [div_mul_cancel h.ne']

theorem lt_div_iff' {x y z : α} (h : 0 < z) : x < y / z ↔ z * x < y := by
  cnsimp only [lt_div_iff h, mul_comm x, iff_self_iff_true]

theorem inv_nonneg_of_nonneg {x : α} (h : 0 ≤ x) : 0 ≤ x⁻¹ := by
  by_cases' h' : x ~= 0
  · cnsimp [h']
  · apply le_of_not_le
    intro h''
    replace h'' := mul_le_mul_of_nonneg_right h'' h
    cnsimp only [zero_mul, inv_mul_cancel h'] at h''
    exact absurd h'' zero_lt_one.not_le

theorem inv_nonneg {x : α} : 0 ≤ x⁻¹ ↔ 0 ≤ x := by
  constructor
  · intro h
    cnsimpa using inv_nonneg_of_nonneg h
  · exact inv_nonneg_of_nonneg

theorem inv_pos_of_pos {x : α} (h : 0 < x) : 0 < x⁻¹ := by
  apply lt_of_not_le
  intro h''
  replace h'' := lt_of_le_of_ne h'' (inv_eq_zero_iff.not.mpr h.ne')
  replace h'' := mul_lt_mul_of_pos_right h'' h
  cnsimp only [zero_mul, inv_mul_cancel h.ne'] at h''
  exact absurd h'' zero_lt_one.not_lt

theorem inv_pos {x : α} : 0 < x⁻¹ ↔ 0 < x := by
  constructor
  · intro h
    cnsimpa using inv_pos_of_pos h
  · exact inv_pos_of_pos

theorem inv_nonpos_of_nonpos {x : α} (h : x ≤ 0) : x⁻¹ ≤ 0 := by
  cnsimpa only [← not_lt, inv_pos] using h

theorem inv_nonpos {x : α} : x⁻¹ ≤ 0 ↔ x ≤ 0 := by
  cnsimp only [← not_lt, inv_pos, iff_self_iff_true]

theorem inv_lt_zero_of_neg {x : α} (h : x < 0) : x⁻¹ < 0 := by
  cnsimpa only [← not_le, inv_nonneg] using h

theorem inv_lt_zero_iff {x : α} : x⁻¹ < 0 ↔ x < 0 := by
  cnsimp only [← not_le, inv_nonneg, iff_self_iff_true]

theorem div_pos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  cnsimpa [div_eq_mul_inv x y] using mul_pos hx (inv_pos_of_pos hy)

theorem div_nonneg {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x / y := by
  cnsimpa [div_eq_mul_inv x y] using mul_nonneg hx (inv_nonneg_of_nonneg hy)

theorem inv_lt_comm {a b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  calc
    a⁻¹ < b ↔ a * a⁻¹ < a * b := (mul_lt_mul_iff_of_pos_left ha).symm
    _ ↔ 1 < a * b := by cnsimp [mul_inv_cancel ha.ne']
    _ ↔ 1 * b⁻¹ < a * b * b⁻¹ := (mul_lt_mul_iff_of_pos_right (inv_pos_of_pos hb)).symm
    _ ↔ b⁻¹ < a := by cnsimp [mul_assoc, mul_inv_cancel hb.ne']

theorem inv_lt_inv_iff {a b : α} (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  cnsimp [inv_lt_comm ha (inv_pos_of_pos hb)]

theorem inv_lt_inv_of_pos {a b : α} (h : a < b) (ha : 0 < a) : b⁻¹ < a⁻¹ :=
  (inv_lt_inv_iff (ha.trans h) ha).mpr h

end Semifield
