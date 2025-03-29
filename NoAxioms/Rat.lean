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

theorem Int.negOfNat_eq' (x : Nat) : negOfNat x = -x := rfl

theorem Int.negSucc_eq'' (x : Nat) : negSucc x = -(x + 1 : Nat) := rfl

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

theorem Nat.mul_ne_zero' {x y : Nat} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  rcases x with (_ | x)
  · contradiction
  rcases y with (_ | y)
  · contradiction
  rw [Nat.succ_mul_succ]
  exact Nat.noConfusion

theorem Int.zero_tdiv' (x : Int) : (0 : Int).tdiv x = 0 := by
  unfold tdiv
  cases x
  · dsimp
    rw [Nat.zero_div', Int.ofNat_zero]
  · dsimp
    rw [Nat.zero_div', Int.ofNat_zero, Int.neg_zero]

theorem Int.mul_ne_zero' {x y : Int} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  intro h
  rw [← Int.mul_tdiv_cancel'' x hy] at hx
  rw [h] at hx
  rw [Int.zero_tdiv'] at hx
  contradiction

theorem Int.mul_eq_zero' {a b : Int} : a * b = 0 ↔ a = 0 ∨' b = 0 := by
  constructor
  · intro h h'
    exact absurd h (Int.mul_ne_zero' h'.1 h'.2)
  · intro h
    refine h.elim (fun h => ?_) (fun h => ?_)
    · rw [h, Int.zero_mul']
    · rw [h, Int.mul_zero]

theorem Int.neg_mul' (x y : Int) : (-x) * y = -(x * y) := by
  rw [Int.mul_comm', Int.mul_neg', Int.mul_comm']

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

instance (x y : Rat) : Decidable (x ~= y) := inferInstanceAs (Decidable (_ = _))

theorem Rat.eqv_def (x y : Rat) : x ~= y ↔ x.num * y.den = y.num * x.den := Iff.rfl

theorem Rat.eqv_of_den_num_eq {x y : Rat} (h : x.num = y.num ∧ x.den = y.den) : x ~= y := by
  cnsimp [Rat.eqv_def]
  rw [h.1, h.2]

def Rat.ofNat (n : Nat) : Rat := ⟨n, 1, Nat.noConfusion⟩

instance : OfNat Rat n := ⟨Rat.ofNat n⟩

theorem Rat.num_ofNat (x : Nat) : (no_index (OfNat.ofNat x : Rat)).num = x := rfl
theorem Rat.den_ofNat (x : Nat) : (no_index (OfNat.ofNat x : Rat)).den = 1 := rfl

protected def Rat.mul : Rat → Rat → Rat
  | ⟨a, b, h1⟩, ⟨c, d, h2⟩ => ⟨a * c, b * d, Nat.mul_ne_zero' h1 h2⟩

@[ccongr]
theorem Rat.mul_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.mul y₁ ~= x₂.mul y₂ := by
  cnsimp [Rat.eqv_def] at *
  unfold Rat.mul
  dsimp
  rw [Int.ofNat_mul, Int.ofNat_mul, ← Int.mul_assoc', ← Int.mul_assoc']
  rw [Int.mul_right_comm' _ y₁.num, hx, Int.mul_assoc', hy, ← Int.mul_assoc']
  rw [Int.mul_right_comm' _ x₁.den]

def Rat.divInt : Int → Int → Rat
  | a, (b + 1 : Nat) => ⟨a, b + 1, Nat.noConfusion⟩
  | _, 0 => 0
  | a, .negSucc b => ⟨-a, b + 1, Nat.noConfusion⟩

protected def Rat.neg : Rat → Rat
  | ⟨a, b, h⟩ => ⟨-a, b, h⟩

@[ccongr]
theorem Rat.neg_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : x₁.neg ~= x₂.neg := by
  cnsimp [eqv_def] at hx ⊢
  dsimp [Rat.neg]
  rw [Int.neg_mul', hx, Int.neg_mul']

@[cnsimp]
theorem Rat.neg_neg (x : Rat) : x.neg.neg ~= x := by
  dsimp [Rat.neg]
  rw [Int.neg_neg]

theorem Rat.divInt_zero_eq (x : Int) : divInt x 0 = 0 := rfl

@[cnsimp]
theorem Rat.divInt_zero (x : Int) : divInt x 0 ~= 0 := by rfl

theorem Rat.neg_divInt_eq (x y : Int) : divInt (-x) y = (divInt x y).neg := by
  unfold divInt
  rcases y with ((_ | y) | y) <;> rfl

theorem Rat.neg_divInt (x y : Int) : divInt (-x) y ~= (divInt x y).neg := by
  rw [Rat.neg_divInt_eq]

theorem Rat.divInt_neg_eq (x y : Int) : divInt x (-y) = (divInt x y).neg := by
  unfold divInt
  rcases y with ((_ | y) | y)
  · rfl
  · rfl
  · rw [Int.neg_negSucc]
    dsimp [Rat.neg]
    rw [Int.neg_neg]

theorem Rat.divInt_neg (x y : Int) : divInt x (-y) ~= (divInt x y).neg := by
  rw [Rat.divInt_neg_eq]

theorem Rat.neg_zero_eq : (0 : Rat).neg = 0 := rfl

@[cnsimp]
theorem Rat.neg_zero : (0 : Rat).neg ~= 0 := by rfl

theorem Rat.neg_divInt_neg_eq (x y : Int) : divInt (-x) (-y) = divInt x y := by
  unfold divInt
  rcases y with ((_ | y) | y)
  · rfl
  · dsimp [← Int.negSucc_eq'']
    rw [Int.neg_neg]
  · rw [Int.neg_negSucc]

theorem Rat.num_divInt_den_eq (x : Rat) : divInt x.num x.den = x := by
  unfold divInt
  rw [← Nat.sub_one_add_one x.den_nz]
  dsimp
  conv => lhs; simp only [Nat.sub_one_add_one x.den_nz]

theorem Rat.mul_divInt_mul_right {x y z : Int} (h : z ≠ 0) : divInt (x * z) (y * z) ~= divInt x y := by
  induction z using Int.negRec with
  | ofNat z =>
    induction x using Int.negRec with
    | ofNat x =>
      induction y using Int.negRec with
      | ofNat y =>
        unfold divInt
        rw [Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat]
        by_cases h' : y = 0
        · cases h'
          rw [Nat.zero_mul]
        · dsimp at h
          cnsimp [Int.ofNat_eq_zero] at h
          rw [← Nat.sub_one_add_one (Nat.mul_ne_zero' h' h)]
          dsimp
          rw [← Nat.sub_one_add_one h']
          dsimp
          cnsimp [eqv_def]
          dsimp
          rw [Nat.sub_one_add_one h', Nat.sub_one_add_one (Nat.mul_ne_zero' h' h)]
          rw [Int.ofNat_mul, Int.ofNat_mul, Int.mul_right_comm', Int.mul_assoc']
      | neg y ih =>
        rw [Int.neg_mul', divInt_neg_eq, divInt_neg_eq]
        cnsimp [ih]
    | neg x ih =>
      rw [Int.neg_mul', neg_divInt_eq, neg_divInt_eq]
      cnsimp [ih]
  | neg z ih =>
    rw [Int.mul_neg', Int.mul_neg', neg_divInt_neg_eq]
    apply ih
    exact (not_congr Int.neg_eq_zero).mp h

theorem Rat.mul_divInt_mul_left {x y z : Int} (h : x ≠ 0) : divInt (x * y) (x * z) ~= divInt y z := by
  rw [Int.mul_comm' x, Int.mul_comm' x]
  exact mul_divInt_mul_right h

protected def Rat.inv : Rat → Rat
  | ⟨a, b, _⟩ => divInt b a

@[ccongr]
theorem Rat.inv_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : x₁.inv ~= x₂.inv := by
  dsimp [Rat.inv]
  cnsimp [eqv_def] at hx
  refine Eq'.trans (y := divInt (x₁.den * x₂.den) (x₁.num * x₂.den)) ?_ ?_
  · cnsimp [Rat.mul_divInt_mul_right x₂.ofNat_den_ne_zero]
  · rw [hx]
    rw [Int.mul_comm']
    cnsimp [Rat.mul_divInt_mul_right x₁.ofNat_den_ne_zero]

theorem Rat.mul_comm (x y : Rat) : x.mul y ~= y.mul x := by
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp
  rw [Int.mul_comm', Nat.mul_comm]
  exact ⟨rfl, rfl⟩

theorem Rat.mul_assoc (x y z : Rat) : (x.mul y).mul z ~= x.mul (y.mul z) := by
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp
  rw [Int.mul_assoc', Nat.mul_assoc']
  exact ⟨rfl, rfl⟩

@[cnsimp]
theorem Rat.mul_one (x : Rat) : x.mul 1 ~= x := by
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp [Rat.ofNat]
  rw [Int.mul_one', Nat.mul_one]
  exact ⟨rfl, rfl⟩

@[cnsimp]
theorem Rat.one_mul (x : Rat) : (1 : Rat).mul x ~= x := by
  cnsimp [Rat.mul_comm 1]

@[cnsimp]
theorem Rat.mul_zero (x : Rat) : x.mul 0 ~= 0 := by
  unfold Rat.mul
  cnsimp only [eqv_def]
  dsimp [Rat.num_ofNat, Rat.den_ofNat, Rat.ofNat]
  rw [Int.mul_zero, Int.zero_mul', Int.zero_mul']

@[cnsimp]
theorem Rat.zero_mul (x : Rat) : (0 : Rat).mul x ~= 0 := by
  cnsimp [Rat.mul_comm 0]

theorem Rat.eq'_zero_iff_num_eq_zero (x : Rat) : x ~= 0 ↔ x.num = 0 := by
  cnsimp only [eqv_def]
  dsimp [Rat.num_ofNat, Rat.den_ofNat]
  rw [Int.mul_one', Int.zero_mul']

theorem Rat.mul_inv_cancel {x : Rat} (h : x ~!= 0) : x.mul x.inv ~= 1 := by
  cnsimp only [eqv_def]
  dsimp [Rat.num_ofNat, Rat.den_ofNat]
  rw [Int.mul_one', Int.one_mul]
  cnsimp only [Rat.eq'_zero_iff_num_eq_zero, ne'_iff] at h
  dsimp [Rat.mul, Rat.inv, divInt]
  split
  · rename_i y hy
    dsimp
    rw [hy, Int.mul_comm']
    rfl
  · contradiction
  · rename_i y hy
    dsimp
    rw [hy, Int.negSucc_mul_negOfNat', Nat.mul_comm]

theorem Rat.inv_mul_cancel {x : Rat} (h : x ~!= 0) : x.inv.mul x ~= 1 := by
  cnsimp [Rat.mul_comm x.inv, Rat.mul_inv_cancel h]

@[cnsimp]
theorem Rat.inv_zero : (0 : Rat).inv ~= 0 := by rfl

theorem Rat.inv_eq_zero_iff {x : Rat} : x.inv ~= 0 ↔ x ~= 0 := by
  constructor
  · intro h
    refine Decidable.by_contra (fun h' => ?_)
    apply h'
    calc
      x ~= x.mul (x.inv.mul x) := by cnsimp [Rat.inv_mul_cancel h']
      _ ~= 0 := by cnsimp [h]
  · intro h
    cnsimp [h]

@[cnsimp]
theorem Rat.inv_inv (x : Rat) : x.inv.inv ~= x := by
  by_cases h : x ~= 0
  · cnsimp [h]
  · have h' := (not_congr Rat.inv_eq_zero_iff).mpr h
    calc
      _ ~= x.inv.inv.mul (x.inv.mul x) := by cnsimp [Rat.inv_mul_cancel h]
      _ ~= (x.inv.inv.mul x.inv).mul x := (Rat.mul_assoc ..).symm
      _ ~= x := by cnsimp [Rat.inv_mul_cancel h']

theorem Rat.mul_right_comm (x y z : Rat) : (x.mul y).mul z ~= (x.mul z).mul y := by
  cnsimp [Rat.mul_assoc, Rat.mul_comm y]

theorem Rat.mul_left_comm (x y z : Rat) : x.mul (y.mul z) ~= y.mul (x.mul z) := by
  cnsimp [Rat.mul_assoc, Rat.mul_comm y]

theorem Rat.mul_right_cancel {x y z : Rat} (h : z ~!= 0) (h' : x.mul z ~= y.mul z) : x ~= y := by
  calc
    x ~= (x.mul z).mul z.inv := by cnsimp [Rat.mul_assoc, Rat.mul_inv_cancel h]
    _ ~= (y.mul z).mul z.inv := by cnsimp [h']
    _ ~= y := by cnsimp [Rat.mul_assoc, Rat.mul_inv_cancel h]

theorem Rat.mul_left_cancel {x y z : Rat} (h : x ~!= 0) (h' : x.mul y ~= x.mul z) : y ~= z := by
  cnsimp only [Rat.mul_comm x] at h'
  exact Rat.mul_right_cancel h h'
