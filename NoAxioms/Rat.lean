import NoAxioms.Prelude

theorem Nat.mul_assoc' (a b c : Nat) : a * b * c = a * (b * c) := by
  induction b with
  | zero => rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.succ_mul, Nat.mul_comm, Nat.mul_add, Nat.mul_comm, ih,
      Nat.mul_add, Nat.mul_comm a c]

theorem Nat.add_right_cancel' {a b c : Nat} (h : a + c = b + c) : a = b := by
  induction c with
  | zero => exact h
  | succ k ih =>
    apply ih
    change a + (k + 1) - 1 = b + (k + 1) - 1
    rw [h]

theorem Nat.div.go_eq (y : Nat) (hy : 0 < y) (fuel x : Nat) (hfuel : x < fuel) :
    Nat.div.go y hy fuel x hfuel = x / y := by
  induction fuel using Nat.strongRecOn generalizing x with
  | ind k ih =>
    unfold go
    rcases k with (_ | ⟨k⟩); contradiction
    change _ = Nat.div _ _
    dsimp
    unfold Nat.div
    rw [dif_pos hy]
    conv => rhs; unfold go
    apply dite_congr rfl
    · intro h
      rw [ih _ hfuel, ih _ (Nat.lt_succ_self _)]
    · intro h
      rfl

theorem Nat.div_eq' (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 := by
  change x.div y = _
  unfold Nat.div
  unfold Nat.div.go
  split
  · split
    · rw [if_pos ⟨‹_›, ‹_›⟩, div.go_eq]
    · rw [if_neg (fun h => absurd h.2 ‹_›)]
  · rw [if_neg (fun h => absurd h.1 ‹_›)]

theorem Nat.zero_div' (x : Nat) : 0 / x = 0 := by
  rw [Nat.div_eq', if_neg]
  intro ⟨h1, h2⟩
  match x, h1, h2 with
  | 0, _, _ => contradiction

theorem Nat.add_sub_add_right' (n k m : Nat) : n + k - (m + k) = n - m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.add_succ, Nat.succ_sub_succ, ih]

theorem Nat.add_sub_cancel_right' {x y : Nat} : x + y - y = x := by
  induction y with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.succ_eq_add_one, Nat.add_sub_add_right', ih]

theorem Nat.add_div_right' {x y : Nat} (hy : 0 < y) : (x + y) / y = x / y + 1 := by
  rw [Nat.div_eq', if_pos]
  · rw [Nat.add_sub_cancel_right']
  · exact ⟨hy, le_add_left y x⟩

theorem Nat.mul_div_cancel'' (a : Nat) {b : Nat} (hb : 0 < b) : a * b / b = a := by
  induction a with
  | zero => rw [Nat.zero_mul, Nat.zero_div']
  | succ k ih => rw [Nat.succ_mul, Nat.add_div_right' hb, ih]

theorem Nat.mul_right_cancel' {a b c : Nat} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  rw [← Nat.mul_div_cancel'' a hc, ← Nat.mul_div_cancel'' b hc, h]

open scoped Int in

theorem Int.negSucc_inj' {m n : Nat} : -[m+1] = -[n+1] ↔ m = n := by
  constructor
  · exact Int.negSucc.inj
  · rintro rfl; rfl

theorem Int.mul_tdiv_cancel'' (a : Int) {b : Int} (h : b ≠ 0) : (a * b).tdiv b = a := by
  change (a.mul b).tdiv b = a
  unfold Int.mul Int.tdiv
  rcases a with (a | a)
  <;> rcases b with (b | b)
  <;> dsimp
  · apply Int.ofNat_inj.mpr
    apply Nat.mul_div_cancel''
    rw [ofNat_eq_coe, ne_eq] at h
    replace h := (not_congr ofNat_eq_zero).mp h
    exact Nat.zero_lt_of_ne_zero h
  · unfold negOfNat
    cases a
    · rw [Nat.zero_mul]
      dsimp
      rw [Nat.zero_div']
      rfl
    · rw [Nat.succ_mul_succ]
      dsimp
      rw [← Nat.succ_mul_succ, Nat.mul_div_cancel'' _ (Nat.zero_lt_succ _)]
  · rw [ofNat_eq_coe, ne_eq] at h
    replace h := (not_congr ofNat_eq_zero).mp h
    unfold negOfNat
    rw (occs := .pos [1]) [← Nat.sub_one_add_one h, Nat.succ_mul_succ]
    dsimp
    rw [← Nat.succ_mul_succ, Nat.succ_eq_add_one (b - 1), Nat.sub_one_add_one h]
    rw [Nat.mul_div_cancel'' _ (Nat.zero_lt_of_ne_zero h)]
    rfl
  · rw [Nat.mul_div_cancel'' _ (Nat.zero_lt_succ _)]
    rfl

theorem Int.mul_right_cancel' {a b c : Int} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  rw [← Int.mul_tdiv_cancel'' a hc, ← Int.mul_tdiv_cancel'' b hc, h]

@[elab_as_elim]
def Int.negRec {motive : Int → Sort u}
    (ofNat : (n : Nat) → motive n) (neg : (n : Int) → motive n → motive (-n))
    (t : Int) : motive t :=
  match t with
  | .ofNat x => ofNat x
  | .negSucc x => neg (x + 1) (ofNat (x + 1))

@[elab_as_elim]
theorem Int.zero_succ_neg_ind {motive : Int → Prop}
    (zero : motive 0) (succ : (n : Int) → motive n → motive (n + 1))
    (neg : (n : Int) → motive n → motive (-n))
    (t : Int) : motive t := by
  refine Int.negRec ?_ neg t
  intro n
  induction n with
  | zero => exact zero
  | succ k ih => exact succ k ih

theorem Int.zero_mul' (a : Int) : 0 * a = 0 := by
  change Int.mul _ _ = _
  unfold Int.mul
  cases a
  · dsimp
    rw [Nat.zero_mul, ofNat_zero]
  · dsimp
    rw [Nat.zero_mul, negOfNat]

theorem Int.mul_neg' (a b : Int) : a * (-b) = -(a * b) := by
  change a.mul b.neg = (a.mul b).neg
  rcases a with (a | a) <;> rcases b with ((_ | b) | b)
  · rfl
  · rfl
  · unfold Int.mul Int.neg
    dsimp
    cases a * (b + 1) <;> rfl
  · dsimp
    rw [Int.mul_zero]
    dsimp [Int.neg, Int.negOfNat]
    rw [Int.mul_zero]
  · rfl
  · rfl

theorem Int.mul_one' (a : Int) : a * 1 = a := by
  change a.mul 1 = a
  unfold Int.mul
  rcases a with (a | a)
  · dsimp
    rw [Nat.mul_one]
  · dsimp
    rw [Nat.mul_one]
    rfl

theorem Int.mul_comm' (a b : Int) : a * b = b * a := by
  change a.mul b = b.mul a
  unfold Int.mul
  rcases a with (a | a) <;> rcases b with (b | b)
  all_goals
  dsimp
  rw [Nat.mul_comm]

theorem Int.add_comm' (a b : Int) : a + b = b + a := by
  change a.add b = b.add a
  unfold Int.add
  rcases a with (a | a) <;> rcases b with (b | b)
  all_goals dsimp
  all_goals rw [Nat.add_comm a]

theorem Int.sub_self' (a : Int) : a - a = 0 := by
  change a.add a.neg = 0
  unfold Int.add Int.neg
  rcases a with ((_ | a) | a)
  · rfl
  · dsimp [negOfNat, subNatNat]
    rw [Nat.sub_self]
    dsimp
  · dsimp [negOfNat, subNatNat]
    rw [Nat.sub_self]
    dsimp

#print axioms Int.sub_self

#print axioms Int.mul_neg

theorem Int.negOfNat_eq' (x : Nat) : negOfNat x = -x := rfl

theorem Int.ofNat_mul_negOfNat' (x y : Nat) : (x * (-y) : Int) = -(x * y : Nat) := by
  rw [← Int.negOfNat_eq', Int.ofNat_mul_negOfNat]
  rfl

theorem Int.negSucc_mul_negOfNat' (x y : Nat) : ((.negSucc x) * -y : Int) = (x.succ * y : Nat) := by
  rw [← Int.negOfNat_eq', Int.negSucc_mul_negOfNat]
  rfl

theorem Int.negOfNat_mul_ofNat' (x y : Nat) : (-x * y : Int) = -(x * y : Nat) := by
  rw [Int.mul_comm', Int.ofNat_mul_negOfNat', Nat.mul_comm]

theorem Int.negOfNat_mul_negSucc' (x y : Nat) : (-x * (.negSucc y) : Int) = (x * y.succ : Nat) := by
  rw [Int.mul_comm', Int.negSucc_mul_negOfNat', Nat.mul_comm]

theorem Int.mul_assoc' (a b c : Int) : a * b * c = a * (b * c) := by
  rcases a with (a | a)
  <;> rcases b with (b | b)
  <;> rcases c with (c | c)
  all_goals simp only [ofNat_eq_coe, Int.ofNat_mul_ofNat, Int.ofNat_mul_negSucc,
    Int.ofNat_mul_negOfNat', Int.negSucc_mul_ofNat, Int.negSucc_mul_negOfNat',
    Int.negSucc_mul_negSucc, Int.negOfNat_mul_ofNat', Int.negOfNat_mul_negSucc']
  all_goals rw [Nat.mul_assoc']

theorem Int.mul_right_comm' (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc', Int.mul_comm' b, Int.mul_assoc']

structure Rat where
  num : Int
  den : Nat
  den_nz : den ≠ 0

theorem Rat.ofNat_den_ne_zero (x : Rat) : (x.den : Int) ≠ 0 :=
  (not_congr Int.ofNat_eq_zero).mpr x.den_nz

theorem Rat.den_pos (x : Rat) : 0 < x.den := Nat.zero_lt_of_ne_zero x.den_nz

instance : Eqv Rat where
  eqv x y := x.num * y.den = y.num * x.den
  refl x := rfl
  symm h := h.symm
  trans {x y z} h h' := by
    dsimp at h h' ⊢
    refine Int.mul_right_cancel' y.ofNat_den_ne_zero ?_
    rw [Int.mul_right_comm', h, Int.mul_right_comm', h', Int.mul_right_comm']

-- ad = bc
-- cf = de
-- af = be
-- adf = bcf = bde

#print axioms Nat.mul_right_cancel
