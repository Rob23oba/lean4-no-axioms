import NoAxioms.IntNatInstances

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
  · dsimp only [ofNat_eq_coe]
    rw [Nat.zero_div', Int.ofNat_zero]
  · dsimp only [ofNat_eq_coe]
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

theorem Int.ofNat_add_negOfNat (x y : Nat) : (x : Int) + -y = subNatNat x y := by
  change Int.add _ _ = _
  unfold Int.add
  cases y
  · dsimp only [cast_ofNat_Int, Int.neg_zero, ofNat_eq_coe, Nat.succ_eq_add_one,
      subNatNat, Nat.sub_zero, Nat.add_zero]
    rw [Nat.zero_sub]
  · rfl

theorem Int.negOfNat_add_ofNat (x y : Nat) : -(x : Int) + y = subNatNat y x := by
  change Int.add _ _ = _
  unfold Int.add
  cases x
  · dsimp only [cast_ofNat_Int, Int.neg_zero, ofNat_eq_coe, Nat.succ_eq_add_one, subNatNat,
      Nat.sub_zero]
    rw [Nat.zero_sub, Nat.zero_add]
  · rfl

theorem Nat.succ_sub' {a b : Nat} (hle : b ≤ a) : a.succ - b = (a - b).succ := by
  induction b generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Nat.succ_sub_succ]
    match a, hle with
    | .succ a', hle' =>
      rw [Nat.succ_sub_succ, ih]
      apply Nat.le_of_succ_le_succ hle'

theorem Nat.eq_add_of_sub_eq' {a b c : Nat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  induction hle generalizing c with
  | refl =>
    rw [Nat.sub_self] at h
    rw [← h, Nat.zero_add]
  | @step m h' ih =>
    rw [Nat.succ_sub' h'] at h
    rw [← h, Nat.succ_add, Nat.sub_add_cancel' h']

theorem Nat.sub_eq_of_eq_add'' {a b c : Nat} (h : a = c + b) : a - b = c := by
  induction b generalizing a c with
  | zero => exact h
  | succ k ih =>
    rw [Nat.add_succ, ← Nat.succ_add] at h
    rw [Nat.sub_succ, ih h, Nat.pred_succ]

theorem Nat.sub_eq_iff_eq_add''' {a b c : Nat} (hle : b ≤ a) : a - b = c ↔ a = c + b := by
  constructor
  · exact Nat.eq_add_of_sub_eq' hle
  · exact Nat.sub_eq_of_eq_add''

theorem Nat.sub_add_comm' {x y z : Nat} (h : z ≤ x) : x + y - z = x - z + y := by
  cnsimp [Nat.sub_eq_iff_eq_add''' (Nat.le_add_right_of_le h)]
  induction h with
  | refl => rw [Nat.sub_self, Nat.add_comm, Nat.zero_add]
  | @step m h ih =>
    rw [Nat.succ_add, ih, Nat.succ_sub' h, Nat.succ_add, Nat.succ_add]

theorem Nat.mul_pred' (x y : Nat) : x * y.pred = x * y - x := by
  induction y with
  | zero => rw [Nat.pred_zero, Nat.mul_zero, Nat.zero_sub]
  | succ k ih =>
    rw [Nat.pred_succ, Nat.mul_succ, Nat.add_sub_cancel_right']

theorem Nat.sub_sub' (x y z : Nat) : x - y - z = x - (y + z) := by
  induction z with
  | zero => rfl
  | succ k ih =>
    rw [Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

theorem Nat.mul_sub' (x y z : Nat) : x * (y - z) = x * y - x * z := by
  induction z with
  | zero => rfl
  | succ k ih =>
    rw [Nat.sub_succ, Nat.mul_pred', ih, Nat.mul_succ, Nat.sub_sub']

theorem Nat.sub_add (x y z : Nat) : x - y - z = x - (y + z) := by
  induction z with
  | zero => rfl
  | succ k ih =>
    rw [Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

theorem Nat.le_max' {x y z : Nat} : x ≤ max y z ↔ x ≤ y ∨' x ≤ z := by
  dsimp only [Nat.max_def]
  split
  · constructor
    · exact Or'.inr
    · rename_i h
      intro h'
      exact h'.elim (trans · h) id
  · constructor
    · exact Or'.inl
    · rename_i h
      intro h'
      exact h'.elim id (trans · (Nat.le_of_not_le h))

theorem Nat.max_le' {x y z : Nat} : max x y ≤ z ↔ x ≤ z ∧ y ≤ z := by
  dsimp only [Nat.max_def]
  split
  · constructor
    · rename_i h
      intro h'
      constructor
      · exact trans h h'
      · exact h'
    · exact And.right
  · constructor
    · rename_i h
      intro h'
      constructor
      · exact h'
      · exact trans (Nat.le_of_not_le h) h'
    · exact And.left

structure Rat where
  num : Int
  den : Nat
  den_nz : den ≠ 0

theorem Rat.ofNat_den_ne_zero (x : Rat) : (x.den : Int) ≠ 0 :=
  (not_congr Int.ofNat_eq_zero).mpr x.den_nz

theorem Rat.den_pos (x : Rat) : 0 < x.den := Nat.zero_lt_of_ne_zero x.den_nz

theorem Rat.ofNat_den_pos (x : Rat) : 0 < (x.den : Int) := by
  match x.den, x.den_pos with
  | y + 1, _ =>
    cnsimp [Int.lt_iff_add_one_le, Int.le_def]
    exact ⟨y⟩

theorem Rat.ofNat_den_nonneg (x : Rat) : 0 ≤ (x.den : Int) :=
  Int.natCast_nonneg x.den

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
theorem Rat.eqv_def' (x y : Rat) : x ~= y ↔ x.num * y.den ~= y.num * x.den := Iff.rfl

theorem Rat.eqv_of_den_num_eq {x y : Rat} (h : x.num = y.num ∧ x.den = y.den) : x ~= y := by
  cnsimp [Rat.eqv_def]
  rw [h.1, h.2]

def Rat.ofNat (n : Nat) : Rat := ⟨n, 1, Nat.noConfusion⟩

instance : OfNat Rat n := ⟨Rat.ofNat n⟩
instance : NatCast Rat := ⟨Rat.ofNat⟩

theorem Rat.num_ofNat (x : Nat) : (no_index (OfNat.ofNat x : Rat)).num = x := rfl
theorem Rat.den_ofNat (x : Nat) : (no_index (OfNat.ofNat x : Rat)).den = 1 := rfl

protected def Rat.mul : Rat → Rat → Rat
  | ⟨a, b, h1⟩, ⟨c, d, h2⟩ => ⟨a * c, b * d, Nat.mul_ne_zero' h1 h2⟩

instance : Mul Rat := ⟨Rat.mul⟩

theorem Rat.mul_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ * y₁ ~= x₂ * y₂ := by
  change x₁.mul y₁ ~= x₂.mul y₂
  cnsimp [Rat.eqv_def] at *
  unfold Rat.mul
  dsimp only [ne_eq, Int.natCast_mul]
  rw [← Int.mul_assoc', ← Int.mul_assoc']
  rw [Int.mul_right_comm' _ y₁.num, hx, Int.mul_assoc', hy, ← Int.mul_assoc']
  rw [Int.mul_right_comm' _ x₁.den]

instance : MulCongr Rat where
  mul_congr := Rat.mul_congr

def Rat.divInt : Int → Int → Rat
  | a, (b + 1 : Nat) => ⟨a, b + 1, Nat.noConfusion⟩
  | _, 0 => 0
  | a, .negSucc b => ⟨-a, b + 1, Nat.noConfusion⟩

@[ccongr]
theorem Rat.divInt_congr {x₁ x₂ y₁ y₂ : Int} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    divInt x₁ y₁ ~= divInt x₂ y₂ :=
  hx ▸ hy ▸ .rfl

protected def Rat.neg : Rat → Rat
  | ⟨a, b, h⟩ => ⟨-a, b, h⟩

instance : Neg Rat := ⟨Rat.neg⟩

protected theorem Rat.neg_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : -x₁ ~= -x₂ := by
  dsimp [Neg.neg]
  cnsimp only [eqv_def'] at hx ⊢
  dsimp [Rat.neg]
  cnsimp [hx]

instance : NegCongr Rat where
  neg_congr := Rat.neg_congr

theorem Rat.divInt_zero_eq (x : Int) : divInt x 0 = 0 := rfl

@[cnsimp]
theorem Rat.divInt_zero (x : Int) : divInt x 0 ~= 0 := by rfl

theorem Rat.neg_divInt_eq (x y : Int) : divInt (-x) y = - divInt x y := by
  rcases y with ((_ | y) | y) <;> rfl

theorem Rat.neg_divInt (x y : Int) : divInt (-x) y ~= - divInt x y := by
  rw [Rat.neg_divInt_eq]

theorem Rat.divInt_neg_eq (x y : Int) : divInt x (-y) = - divInt x y := by
  unfold divInt
  rcases y with ((_ | y) | y)
  · rfl
  · rfl
  · rw [Int.neg_negSucc]
    dsimp only [Nat.succ_eq_add_one]
    change _ = Rat.neg _
    dsimp [Rat.neg]
    rw [Int.neg_neg]

theorem Rat.divInt_neg (x y : Int) : divInt x (-y) ~= - divInt x y := by
  rw [Rat.divInt_neg_eq]

theorem Rat.neg_divInt_neg_eq (x y : Int) : divInt (-x) (-y) = divInt x y := by
  unfold divInt
  rcases y with ((_ | y) | y)
  · rfl
  · dsimp only [Int.ofNat_eq_coe, ← Int.negSucc_eq'']
    rw [Int.neg_neg]
  · rw [Int.neg_negSucc]

theorem Rat.neg_divInt_neg (x y : Int) : divInt (-x) (-y) ~= divInt x y := by
  rw [Rat.neg_divInt_neg_eq]

theorem Rat.num_divInt_den_eq (x : Rat) : divInt x.num x.den = x := by
  unfold divInt
  rw [← Nat.sub_one_add_one x.den_nz]
  dsimp only
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
          dsimp only
          rw [← Nat.sub_one_add_one h']
          dsimp only
          cnsimp [eqv_def]
          dsimp only
          rw [Nat.sub_one_add_one h', Nat.sub_one_add_one (Nat.mul_ne_zero' h' h)]
          rw [Int.natCast_mul, Int.natCast_mul, Int.mul_right_comm', Int.mul_assoc']
      | neg y ih =>
        cnsimp [divInt_neg, ih]
    | neg x ih =>
      cnsimp [neg_divInt, ih]
  | neg z ih =>
    cnsimp [neg_divInt_neg, ih (Int.neg_eq_zero.not.mp h)]

theorem Rat.mul_divInt_mul_left {x y z : Int} (h : x ≠ 0) : divInt (x * y) (x * z) ~= divInt y z := by
  rw [Int.mul_comm' x, Int.mul_comm' x]
  exact mul_divInt_mul_right h

protected def Rat.inv : Rat → Rat
  | ⟨a, b, _⟩ => divInt b a

protected theorem Rat.inv_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : x₁.inv ~= x₂.inv := by
  dsimp [Rat.inv]
  cnsimp [eqv_def] at hx
  refine Eq'.trans (y := divInt (x₁.den * x₂.den) (x₁.num * x₂.den)) ?_ ?_
  · cnsimp [Rat.mul_divInt_mul_right x₂.ofNat_den_ne_zero]
  · rw [hx]
    rw [Int.mul_comm']
    cnsimp [Rat.mul_divInt_mul_right x₁.ofNat_den_ne_zero]

instance : Inv Rat := ⟨Rat.inv⟩
instance : InvCongr Rat := ⟨Rat.inv_congr⟩

protected def Rat.div (x y : Rat) := x * y⁻¹

instance : Div Rat := ⟨Rat.div⟩

protected theorem Rat.div_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ / y₁ ~= x₂ / y₂ := by
  dsimp [· / ·, Div.div, Rat.div]
  ccongr <;> assumption

instance : DivCongr Rat where
  div_congr := Rat.div_congr

@[deprecated "a" (since := "")]
protected theorem Rat.mul_comm (x y : Rat) : x * y ~= y * x := by
  change Rat.mul _ _ ~= Rat.mul _ _
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp
  rw [Int.mul_comm', Nat.mul_comm]
  exact ⟨rfl, rfl⟩

@[deprecated "a" (since := "")]
protected theorem Rat.mul_assoc (x y z : Rat) : x * y * z ~= x * (y * z) := by
  change (x.mul y).mul z ~= x.mul (y.mul z)
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp
  rw [Int.mul_assoc', Nat.mul_assoc']
  exact ⟨rfl, rfl⟩

@[deprecated "a" (since := "")]
protected theorem Rat.mul_one (x : Rat) : x * 1 ~= x := by
  change x.mul 1 ~= x
  unfold Rat.mul
  apply eqv_of_den_num_eq
  dsimp [Rat.ofNat]
  rw [Int.mul_one', Nat.mul_one]
  exact ⟨rfl, rfl⟩

set_option linter.deprecated false in
@[deprecated "a" (since := "")]
protected theorem Rat.one_mul (x : Rat) : 1 * x ~= x := by
  cnsimp [Rat.mul_comm 1, Rat.mul_one]

@[deprecated "a" (since := "")]
protected theorem Rat.mul_zero (x : Rat) : x * 0 ~= 0 := by
  change x.mul 0 ~= 0
  unfold Rat.mul
  cnsimp only [eqv_def]
  dsimp [Rat.num_ofNat, Rat.den_ofNat, Rat.ofNat]
  rw [Int.mul_zero, Int.zero_mul', Int.zero_mul']

set_option linter.deprecated false in
@[deprecated "a" (since := "")]
protected theorem Rat.zero_mul (x : Rat) : 0 * x ~= 0 := by
  cnsimp [Rat.mul_comm 0, Rat.mul_zero]

theorem Rat.eq'_zero_iff_num_eq_zero (x : Rat) : x ~= 0 ↔ x.num = 0 := by
  cnsimp only [eqv_def]
  dsimp [Rat.num_ofNat, Rat.den_ofNat]
  rw [Int.mul_one', Int.zero_mul']

theorem Rat.eq'_zero_iff_num_eq'_zero (x : Rat) : x ~= 0 ↔ x.num ~= 0 :=
  Rat.eq'_zero_iff_num_eq_zero x

@[deprecated "a" (since := "")]
protected theorem Rat.inv_mul_cancel {x : Rat} (h : x ~!= 0) : x⁻¹ * x ~= 1 := by
  change x.inv.mul x ~= 1
  cnsimp only [eqv_def]
  dsimp only [den_ofNat, Int.cast_ofNat_Int, num_ofNat]
  rw [Int.mul_one', Int.one_mul]
  cnsimp only [Rat.eq'_zero_iff_num_eq_zero, ne'_iff] at h
  dsimp only [Rat.inv, divInt, Rat.mul]
  split
  · rename_i y hy
    dsimp
    rw [hy, Int.mul_comm']
    rfl
  · contradiction
  · rename_i y hy
    dsimp only
    rw [hy, Int.negOfNat_mul_negSucc', Nat.mul_comm]

set_option linter.deprecated false in
instance : CommGroupWithZero Rat where
  mul_zero := Rat.mul_zero
  zero_mul := Rat.zero_mul
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := .intro 0 (.intro 1 (by decide))
  inv_zero := rfl
  inv_mul_cancel _ := Rat.inv_mul_cancel

protected def Rat.add : Rat → Rat → Rat
  | ⟨a, b, h⟩, ⟨c, d, h'⟩ => ⟨a * d + b * c, b * d, Nat.mul_ne_zero' h h'⟩

instance : Add Rat := ⟨Rat.add⟩

protected theorem Rat.add_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ + y₁ ~= x₂ + y₂ := by
  dsimp [· + ·, Add.add]
  unfold Rat.add
  dsimp only
  cnsimp only [eqv_def] at *
  dsimp only [Int.natCast_mul]
  rw [Int.add_mul', Int.add_mul']
  simp only [← Int.mul_assoc']
  rw [Int.mul_right_comm' x₁.num, hx]
  rw [Int.mul_right_comm' _ _ y₂.den, Int.mul_right_comm' x₂.num]
  rw [Int.mul_comm' x₁.den, Int.mul_right_comm' _ _ y₂.den]
  rw [Int.mul_right_comm' _ _ y₂.den, hy, Int.mul_right_comm' _ _ x₂.den]
  rw [Int.mul_right_comm' _ _ x₂.den, Int.mul_right_comm' _ y₁.den x₁.den]
  rw [Int.mul_comm' y₂.num]

instance : AddCongr Rat where
  add_congr := Rat.add_congr

protected def Rat.sub (x y : Rat) := x + -y

instance : Sub Rat := ⟨Rat.sub⟩

protected theorem Rat.sub_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ - y₁ ~= x₂ - y₂ := by
  dsimp [· - ·, Sub.sub, Rat.sub]
  ccongr <;> assumption

instance : SubCongr Rat where
  sub_congr := Rat.sub_congr

@[deprecated "a" (since := "")]
protected theorem Rat.neg_add_cancel (x : Rat) : -x + x ~= 0 := by
  change x.neg.add x ~= 0
  unfold Rat.add Rat.neg
  dsimp
  cnsimp [eq'_zero_iff_num_eq'_zero]
  dsimp
  cnsimp [mul_comm x.num]

@[deprecated "a" (since := "")]
protected theorem Rat.add_comm (x y : Rat) : x + y ~= y + x := by
  change x.add y ~= y.add x
  unfold Rat.add
  apply eqv_of_den_num_eq
  dsimp
  rw [Int.add_comm', Int.mul_comm', Int.mul_comm' x.num, Nat.mul_comm x.den]
  exact ⟨rfl, rfl⟩

@[deprecated "a" (since := "")]
protected theorem Rat.add_zero (x : Rat) : x + 0 ~= x := by
  change x.add 0 ~= x
  unfold Rat.add
  apply eqv_of_den_num_eq
  dsimp [ofNat]
  rw [Int.mul_one', Int.mul_zero, Int.add_zero, Nat.mul_one]
  exact ⟨rfl, rfl⟩

set_option linter.deprecated false in
@[deprecated "a" (since := "")]
protected theorem Rat.zero_add (x : Rat) : 0 + x ~= x := by
  cnsimp [Rat.add_comm 0, Rat.add_zero]

@[deprecated "a" (since := "")]
protected theorem Rat.add_assoc (x y z : Rat) : x + y + z ~= x + (y + z) := by
  change (x.add y).add z ~= x.add (y.add z)
  unfold Rat.add
  apply eqv_of_den_num_eq
  dsimp only [Int.natCast_mul]
  rw [Int.mul_add', Int.add_mul', Int.mul_assoc', Int.mul_assoc',
    Int.mul_assoc', Int.add_assoc', Nat.mul_assoc']
  exact ⟨rfl, rfl⟩

set_option linter.deprecated false in
instance : AddCommGroup Rat where
  add_zero := Rat.add_zero
  zero_add := Rat.zero_add
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Rat.neg_add_cancel

protected theorem Rat.add_mul (x y z : Rat) : (x + y) * z ~= x * z + y * z := by
  change (x.add y).mul z ~= (x.mul z).add (y.mul z)
  cnsimp [eqv_def]
  unfold Rat.add Rat.mul
  dsimp only [Int.natCast_mul]
  rw [Int.add_mul', Int.add_mul', Int.add_mul']
  simp only [← Int.mul_assoc']
  rw [Int.mul_right_comm' x.num]
  rw [Int.mul_right_comm' _ x.den]
  rw [Int.mul_right_comm' x.den z.den y.num]
  rw [Int.mul_right_comm' _ z.den z.num]
  conv => rhs; rhs; rw [Int.mul_right_comm' _ z.den x.den]

protected theorem Rat.mul_add (x y z : Rat) : x * (y + z) ~= x * y + x * z := by
  cnsimp [mul_comm x, Rat.add_mul]

instance : Ring Rat where
  natCast_zero := rfl
  natCast_succ n := by
    apply Rat.eqv_of_den_num_eq
    dsimp only [NatCast.natCast, · + ·, Add.add]
    dsimp only [Rat.ofNat, Rat.add, ← Int.natCast_mul, ← Int.natCast_add]
    rw [Nat.mul_one]
    exact ⟨rfl, rfl⟩
  mul_add := Rat.mul_add
  add_mul := Rat.add_mul
  mul_zero := mul_zero
  zero_mul := zero_mul

instance : CommRing Rat where
  mul_comm := mul_comm

instance : Field Rat where

theorem Rat.add_div (x y z : Rat) : (x + y) / z ~= x / z + y / z := by
  cnsimp [div_eq_mul_inv, add_mul]

theorem Rat.sub_div (x y z : Rat) : (x - y) / z ~= x / z - y / z := by
  cnsimp [div_eq_mul_inv, sub_mul]

def Rat.le : Rat → Rat → Prop
  | ⟨a, b, _⟩, ⟨c, d, _⟩ => a * d ≤ c * b

def Rat.lt : Rat → Rat → Prop
  | ⟨a, b, _⟩, ⟨c, d, _⟩ => a * d < c * b

instance : LE Rat where
  le := Rat.le

instance : LT Rat where
  lt := Rat.lt

instance (x y : Rat) : Decidable (x ≤ y) := inferInstanceAs (Decidable ((_ : Int) ≤ _))
instance (x y : Rat) : DNE (x ≤ y) := inferInstanceAs (DNE ((_ : Int) ≤ _))

instance (x y : Rat) : Decidable (x < y) := inferInstanceAs (Decidable ((_ : Int) < _))
instance (x y : Rat) : DNE (x < y) := inferInstanceAs (DNE ((_ : Int) < _))

theorem Rat.le_def {x y : Rat} : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := Iff.rfl

theorem Rat.lt_def {x y : Rat} : x < y ↔ x.num * y.den < y.num * x.den := Iff.rfl

theorem Rat.le_refl (x : Rat) : x ≤ x := by
  cnsimp [Rat.le_def]

theorem Rat.le_antisymm {x y : Rat} (h : x ≤ y) (h' : y ≤ x) : x ~= y := by
  cnsimp [Rat.le_def, eqv_def] at *
  exact Int.le_antisymm' h h'

theorem Rat.le_trans {x y z : Rat} (h : x ≤ y) (h' : y ≤ z) : x ≤ z := by
  cnsimp only [Rat.le_def] at *
  apply Int.le_of_mul_le_mul_right' y.ofNat_den_pos
  rw [Int.mul_right_comm']
  refine Int.le_trans' (y := y.num * x.den * z.den) ?_ ?_
  · exact mul_le_mul_of_nonneg_right h (le_of_lt z.ofNat_den_pos)
  rw [Int.mul_right_comm']
  refine Int.le_trans' (y := z.num * y.den * x.den) ?_ ?_
  · exact mul_le_mul_of_nonneg_right h' (le_of_lt x.ofNat_den_pos)
  rw [Int.mul_right_comm']

theorem Rat.le_of_eq' {x y : Rat} (h : x ~= y) : x ≤ y := by
  cnsimp only [Rat.le_def, Rat.eqv_def] at *
  rw [h]

theorem Rat.le_of_not_le {x y : Rat} (h : ¬x ≤ y) : y ≤ x := by
  cnsimp only [Rat.le_def] at *
  exact Int.le_of_not_le' h

instance : LinearOrder Rat where
  le_of_eq _ _ := Rat.le_of_eq'
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_of_not_le _ _ := Rat.le_of_not_le
  lt_iff_le_not_le _ _ := by
    cnsimp only [Rat.le_def, Rat.lt_def]
    exact Preorder.lt_iff_le_not_le ..

theorem Rat.le_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ ≤ y₁ ↔ x₂ ≤ y₂ := by
  constructor
  · intro h
    exact le_of_le_of_eq' (le_of_eq'_of_le hx.symm h) hy
  · intro h
    exact le_of_le_of_eq' (le_of_eq'_of_le hx h) hy.symm

instance : LECongr Rat where
  le_congr := Rat.le_congr

theorem Int.add_le_add_right' {a b c : Int} (h : a ≤ b) : a + c ≤ b + c := by
  cnsimp only [Int.le_def, Int.nonneg_def] at h ⊢
  rcases h with ⟨x, (hx : _ ~= (_ : Int))⟩
  exists x
  change _ ~= (_ : Int)
  cnsimp [hx]

theorem Int.add_le_add_left' {a b c : Int} (h : b ≤ c) : a + b ≤ a + c := by
  rw [Int.add_comm' a, Int.add_comm' a]
  exact Int.add_le_add_right' h

protected theorem Rat.add_le_add_right {x y z : Rat} (h : x ≤ y) : x + z ≤ y + z := by
  cnsimp only [Rat.le_def] at *
  dsimp only [· + ·, Add.add]
  dsimp only [Rat.add, Int.natCast_mul]
  rw [Int.add_mul', Int.add_mul', ← Int.mul_assoc', ← Int.mul_assoc',
    ← Int.mul_assoc', ← Int.mul_assoc']
  rw [Int.mul_right_comm' y.num, Int.mul_right_comm' x.num]
  rw [← Int.add_mul', ← Int.add_mul']
  apply mul_le_mul_of_nonneg_right _ z.ofNat_den_nonneg
  rw [Int.mul_right_comm' x.den, Int.mul_comm' x.den, Int.mul_right_comm' y.den]
  apply Int.add_le_add_right'
  exact mul_le_mul_of_nonneg_right h z.ofNat_den_nonneg

protected theorem Rat.add_le_add_iff_right {x y z : Rat} : x + z ≤ y + z ↔ x ≤ y := by
  constructor
  · intro h
    calc
      x ~= x + z + -z := by cnsimp [add_assoc]
      _ ≤ y + z + -z := Rat.add_le_add_right h
      _ ~= y := by cnsimp [add_assoc]
  · exact Rat.add_le_add_right

protected theorem Rat.le_of_add_le_add_right {x y z : Rat} (h : x + z ≤ y + z) : x ≤ y := by
  exact Rat.add_le_add_iff_right.mp h

protected theorem Rat.num_mul (x y : Rat) : (x * y).num = x.num * y.num := rfl
protected theorem Rat.den_mul (x y : Rat) : (x * y).den = x.den * y.den := rfl

protected theorem Rat.le_of_mul_le_mul_right {x y z : Rat} (h : 0 < z) (h' : x * z ≤ y * z) : x ≤ y := by
  cnsimp only [Rat.le_def] at *
  dsimp only [Rat.num_mul, Rat.den_mul, Int.natCast_mul] at h'
  cnrw [← mul_assoc, mul_right_comm x.num, mul_right_comm y.num, mul_assoc _ z.num] at h'
  apply le_of_mul_le_mul_right h'
  cnsimp only [Rat.lt_def] at h
  dsimp [num_ofNat, den_ofNat] at h
  cnsimp only [zero_mul, mul_one] at h
  exact mul_pos h z.ofNat_den_pos

instance : IsStrictOrderedRing Rat where
  le_of_add_le_add_right _ _ _ := Rat.le_of_add_le_add_right
  le_of_mul_le_mul_right _ _ _ := Rat.le_of_mul_le_mul_right
  le_of_mul_le_mul_left a b c h h' := by
    cnrw [mul_comm] at h'
    exact Rat.le_of_mul_le_mul_right h h'
  zero_le_one := by decide

def Rat.abs : Rat → Rat
  | ⟨x, y, h⟩ => ⟨x.natAbs, y, h⟩

theorem Rat.abs_nonneg (x : Rat) : 0 ≤ x.abs := by
  cnsimp only [Rat.le_def]
  dsimp [Rat.abs, Rat.num_ofNat, Rat.den_ofNat]
  rw [Int.zero_mul', Int.mul_one']
  exact Int.natCast_nonneg _

theorem Rat.abs_of_nonneg {x : Rat} (h : 0 ≤ x) : x.abs ~= x := by
  cnsimp only [Rat.le_def] at h
  dsimp [Rat.abs, Rat.num_ofNat, Rat.den_ofNat] at h
  rw [Int.zero_mul', Int.mul_one'] at h
  apply Rat.eqv_of_den_num_eq
  dsimp [Rat.abs]
  cnsimp only [eq_self_iff_true, and_true_iff]
  cnsimp only [Int.le_def, sub_zero] at h
  match x.num, h with
  | .ofNat x, _ => rfl

@[cnsimp]
theorem Rat.abs_neg (x : Rat) : (-x).abs ~= x.abs := by
  apply Rat.eqv_of_den_num_eq
  dsimp [Rat.abs, Rat.neg]
  cnsimp only [eq_self_iff_true, and_true_iff]
  rcases x.num with ((_ | x) | x) <;> rfl

theorem Rat.abs_of_nonpos {x : Rat} (h : x ≤ 0) : x.abs ~= -x := by
  calc
    x.abs ~= (-x).abs := by cnsimp
    _ ~= -x := Rat.abs_of_nonneg (neg_nonneg.mpr h)

@[ccongr]
theorem Rat.abs_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : x₁.abs ~= x₂.abs := by
  by_cases' h : 0 ≤ x₁
  · cnsimp [Rat.abs_of_nonneg h, Rat.abs_of_nonneg (le_of_le_of_eq' h hx), hx]
  · replace h := Rat.le_of_not_le h
    cnsimp [Rat.abs_of_nonpos h, Rat.abs_of_nonpos (le_of_eq'_of_le hx.symm h), hx]

theorem Rat.abs_le {x y : Rat} : x.abs ≤ y ↔ x ≤ y ∧ -x ≤ y := by
  by_cases' h : 0 ≤ x
  · cnsimp only [Rat.abs_of_nonneg h]
    have h' : -x ≤ 0 := neg_nonpos.mpr h
    constructor
    · intro h''
      constructor
      · assumption
      · exact h'.trans (h.trans h'')
    · intro h''
      exact h''.1
  · replace h := le_of_not_le h
    cnsimp only [Rat.abs_of_nonpos h]
    have h' : 0 ≤ -x := neg_nonneg.mpr h
    constructor
    · intro h''
      constructor
      · exact h.trans (h'.trans h'')
      · assumption
    · intro h''
      exact h''.2

theorem Rat.le_abs {x y : Rat} : x ≤ y.abs ↔ x ≤ y ∨' x ≤ -y := by
  by_cases' h : 0 ≤ y
  · cnsimp only [Rat.abs_of_nonneg h]
    constructor
    · exact Or'.inl
    · intro h'
      refine h'.elim id (fun h'' => ?_)
      exact Rat.le_trans h'' (Rat.le_trans (neg_nonpos.mpr h) h)
  · replace h := Rat.le_of_not_le h
    cnsimp only [Rat.abs_of_nonpos h]
    constructor
    · exact Or'.inr
    · intro h'
      refine h'.elim (fun h'' => ?_) id
      exact Rat.le_trans h'' (Rat.le_trans h (neg_nonneg.mpr h))

theorem Rat.abs_lt {x y : Rat} : x.abs < y ↔ x < y ∧ -x < y := by
  cnsimp only [← not_le, Rat.le_abs, not_or', iff_self_iff_true]

theorem Rat.lt_abs {x y : Rat} : x < y.abs ↔ x < y ∨' x < -y := by
  cnsimp only [← not_le, Rat.abs_le, not_and_iff_not_or_not, iff_self_iff_true]

theorem Rat.half_add_half (x : Rat) : x / 2 + x / 2 ~= x := by
  calc
    _ ~= x * (2⁻¹ + 2⁻¹) := by cnsimp only [div_eq_mul_inv, ← mul_add, eq'_self_iff]
    _ ~= x * 1 := by ccongr <;> rfl
    _ ~= x := by cnsimp

theorem Rat.abs_sub_comm (x y : Rat) : (x - y).abs ~= (y - x).abs := by
  calc
    (x - y).abs ~= (-(x - y)).abs := (Rat.abs_neg _).symm
    _ ~= (y - x).abs := by cnsimp only [neg_sub, eq'_self_iff]

theorem Rat.abs_sub_lt_trans {x y z a b : Rat} (h : (y - x).abs < a) (h' : (z - y).abs < b) :
    (z - x).abs < a + b := by
  cnsimp only [Rat.abs_lt, neg_sub] at *
  constructor
  · have := add_lt_add h.1 h'.1.le
    cnsimp [sub_eq_add_neg, ← add_assoc, (add_right_comm · · (-y)), add_comm (-x)] at this
    exact this
  · have := add_lt_add h.2 h'.2.le
    cnsimp [← add_sub_assoc] at this
    exact this

theorem Rat.abs_add_lt {x y a b : Rat} (h : x.abs < a) (h' : y.abs < b) : (x + y).abs < a + b := by
  cnsimp only [Rat.abs_lt] at *
  constructor
  · exact add_lt_add h.1 h'.1.le
  · cnsimp only [neg_add_rev, add_comm (-y)]
    exact add_lt_add h.2 h'.2.le

@[cnsimp]
theorem Rat.abs_ofNat (n : Nat) : Rat.abs (no_index (OfNat.ofNat n)) ~= no_index (OfNat.ofNat n) := by
  rfl

theorem Rat.natCast_zero : ((0 : Nat) : Rat) ~= 0 := by rfl
@[cnsimp] theorem Rat.natCast_ofNat : ((no_index (OfNat.ofNat n) : Nat) : Rat) ~= no_index (OfNat.ofNat n) := by rfl

theorem Rat.abs_zero : Rat.abs 0 ~= 0 := by
  rfl

/-
theorem Rat.something_inv_cauSeq {a b c d e : Rat}
    (he : 0 < e)
    (ha : (a - b).abs < sorry)
    (hb : (c - d).abs < sorry) :
    (a * c - b * d).abs < e := by
  sorry

theorem Rat.abs_inv_sub_inv_lt {a b x y : Rat}
    (ha : 0 < a) (hb : 0 < b) (hx : a < x) (hy : a < y)
    (hxy : (x - y).abs < b) : (x⁻¹ - y⁻¹).abs < a⁻¹ - (a + b)⁻¹ := by
  cnsimp only [Rat.abs_lt, Rat.neg_sub] at hxy ⊢
  have xpos := Rat.lt_trans ha hx
  have ypos := Rat.lt_trans ha hy
  have : 0 < x * y * a * (a + b) :=
    Rat.mul_pos (Rat.mul_pos (Rat.mul_pos xpos ypos) ha) (Rat.add_pos ha hb)
  constructor
  · refine Rat.lt_of_mul_lt_mul_right ?_ (Rat.le_of_lt this)
    cnsimp only [Rat.sub_mul, ← Rat.mul_assoc, Rat.inv_mul_cancel (Rat.ne_of_gt xpos),
      Rat.one_mul, Rat.mul_right_comm y⁻¹ x y, Rat.inv_mul_cancel (Rat.ne_of_gt ypos)]
    cnsimp only [(Rat.mul_right_comm · · a), Rat.inv_mul_cancel (Rat.ne_of_gt ha), Rat.one_mul]
    cnsimp only [(Rat.mul_right_comm · · (a + b)),
      Rat.inv_mul_cancel (Rat.ne_of_gt (Rat.add_pos ha hb)), Rat.one_mul]
    cnsimp only [Rat.mul_add, add_mul]
    cnsimp only [Rat.lt_sub_iff_add_lt, ← Rat.add_sub_comm]
    cnsimp only [Rat.sub_lt_iff_lt_add, ← Rat.add_assoc]
    cnsimp only [Rat.sub_lt_iff_lt_add] at hxy
    cnsimp only [Rat.mul_comm a x]
    cnsimp only [Rat.add_comm (x * a * y), (Rat.add_right_comm · (x * a * y))]
    cnsimp only [Rat.add_lt_add_iff_right]

theorem Rat.dafda {a b x y : Rat}
    (ha : 0 < a) (hb : 0 < b) (hx : a < x) (hy : y < b) :
    x⁻¹ - (x + y)⁻¹ < a⁻¹ - (a + b)⁻¹ := by
  have this := Rat.abs_inv_sub_inv_lt ha hb hx
  apply Rat.lt_of_mul_lt_mul_right
-/

def Rat.max (x y : Rat) : Rat :=
  if x ≤ y then y else x

def Rat.min (x y : Rat) : Rat :=
  if x ≤ y then x else y

theorem Rat.max_le {x y z : Rat} : x.max y ≤ z ↔ x ≤ z ∧ y ≤ z := by
  dsimp [max]
  split
  · constructor
    · rename_i h
      intro h'
      exact ⟨Rat.le_trans h h', h'⟩
    · exact And.right
  · constructor
    · rename_i h
      intro h'
      exact ⟨h', Rat.le_trans (Rat.le_of_not_le h) h'⟩
    · exact And.left

theorem Rat.le_max_left (x y : Rat) : x ≤ x.max y := by
  dsimp [max]
  split
  · assumption
  · exact Rat.le_refl x

theorem Rat.le_max_right (x y : Rat) : y ≤ x.max y := by
  dsimp [max]
  split
  · exact Rat.le_refl y
  · exact Rat.le_of_not_le ‹_›

@[ccongr]
theorem ite_congr' {p₁ p₂ : Prop} [Decidable p₁] [Decidable p₂]
    {t₁ t₂ e₁ e₂ : α} [Eqv α] (hp : p₁ ↔ p₂) (ht : t₁ ~= t₂) (he : e₁ ~= e₂) :
    (if p₁ then t₁ else e₁) ~= (if p₂ then t₂ else e₂) := by
  split
  · rw [if_pos (hp.mp ‹_›)]
    exact ht
  · rw [if_neg ((not_congr hp).mp ‹_›)]
    exact he

@[ccongr]
theorem Rat.max_congr {x₁ x₂ y₁ y₂ : Rat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.max y₁ ~= x₂.max y₂ := by
  dsimp [max]
  ccongr <;> assumption

theorem Rat.le_max_of_le_left {x y z : Rat} (h : x ≤ y) : x ≤ y.max z := by
  dsimp [max]
  split
  · exact trans h ‹_›
  · assumption

theorem Rat.le_max_right_le_right {x y z : Rat} (h : x ≤ z) : x ≤ y.max z := by
  dsimp [max]
  split
  · assumption
  · exact trans h (Rat.le_of_not_le ‹_›)

theorem Rat.lt_max_of_lt_left {x y z : Rat} (h : x < y) : x < y.max z := by
  dsimp [max]
  split
  · exact trans h ‹_›
  · assumption

theorem Rat.lt_max_of_lt_right {x y z : Rat} (h : x < z) : x < y.max z := by
  dsimp [max]
  split
  · assumption
  · exact trans h (Rat.le_of_not_le ‹_›)

theorem Rat.le_min {x y z : Rat} : x ≤ y.min z ↔ x ≤ y ∧ x ≤ z := by
  dsimp [min]
  split
  · constructor
    · rename_i h
      intro h'
      exact ⟨h', Rat.le_trans h' h⟩
    · exact And.left
  · constructor
    · rename_i h
      intro h'
      exact ⟨Rat.le_trans h' (Rat.le_of_not_le h), h'⟩
    · exact And.right

theorem Rat.min_le_of_left_le {x y z : Rat} (h : x ≤ z) : x.min y ≤ z := by
  dsimp [min]
  split
  · assumption
  · exact trans (Rat.le_of_not_le ‹_›) h

theorem Rat.min_le_of_right_le {x y z : Rat} (h : y ≤ z) : x.min y ≤ z := by
  dsimp [min]
  split
  · exact trans ‹_› h
  · assumption

theorem Rat.lt_min {x y z : Rat} : x < y.min z ↔ x < y ∧ x < z := by
  dsimp [min]
  split
  · constructor
    · rename_i h
      intro h'
      exact ⟨h', trans h' h⟩
    · exact And.left
  · constructor
    · rename_i h
      intro h'
      exact ⟨trans h' (Rat.le_of_not_le h), h'⟩
    · exact And.right

theorem Rat.min_lt_of_left_lt {x y z : Rat} (h : x < z) : x.min y < z := by
  dsimp [min]
  split
  · assumption
  · exact trans (Rat.le_of_not_le ‹_›) h

theorem Rat.min_lt_of_right_lt {x y z : Rat} (h : y < z) : x.min y < z := by
  dsimp [min]
  split
  · exact trans ‹_› h
  · assumption

theorem Rat.le_abs_self (x : Rat) : x ≤ x.abs := by
  cnsimp [Rat.le_abs]

theorem Rat.neg_abs_le_self (x : Rat) : -x.abs ≤ x := by
  cnsimp [neg_le_comm x.abs, Rat.le_abs]

theorem Rat.neg_le_abs_self (x : Rat) : -x ≤ x.abs := by
  cnsimp only [Rat.le_abs]
  exact Or'.inr (Rat.le_refl _)

theorem Rat.abs_sub_abs_le (x y : Rat) : x.abs - y.abs ≤ (x - y).abs := by
  by_cases' h : 0 ≤ x
  · cnsimp only [Rat.abs_of_nonneg h, Rat.le_abs]
    apply Or'.inl
    apply sub_le_sub_left
    exact Rat.le_abs_self _
  · replace h := Rat.le_of_not_le h
    cnsimp only [Rat.abs_of_nonpos h, Rat.le_abs, neg_sub]
    apply Or'.inr
    cnsimp only [sub_eq_add_neg, add_comm (-x), Rat.add_le_add_iff_right]
    exact Rat.neg_abs_le_self y

theorem Rat.abs_mul (x y : Rat) : (x * y).abs ~= x.abs * y.abs := by
  by_cases' h : 0 ≤ x
  · cnsimp only [Rat.abs_of_nonneg h]
    by_cases' h' : 0 ≤ y
    · cnsimp [Rat.abs_of_nonneg h', Rat.abs_of_nonneg (mul_nonneg h h')]
    · replace h' := Rat.le_of_not_le h'
      cnsimp [Rat.abs_of_nonpos h', Rat.abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h h')]
  · replace h := Rat.le_of_not_le h
    cnsimp only [Rat.abs_of_nonpos h]
    by_cases' h' : 0 ≤ y
    · cnsimp [Rat.abs_of_nonneg h', Rat.abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h h')]
    · replace h' := Rat.le_of_not_le h'
      cnsimp [Rat.abs_of_nonpos h', Rat.abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos h h')]

theorem Rat.abs_inv (x : Rat) : x⁻¹.abs ~= x.abs⁻¹ := by
  by_cases' h : 0 ≤ x
  · cnsimp [Rat.abs_of_nonneg h, Rat.abs_of_nonneg (inv_nonneg_of_nonneg h)]
  · replace h := Rat.le_of_not_le h
    cnsimp [Rat.abs_of_nonpos h, Rat.abs_of_nonpos (inv_nonpos_of_nonpos h), inv_neg]

theorem Rat.abs_div (x y : Rat) : (x / y).abs ~= x.abs / y.abs := by
  cnsimp [div_eq_mul_inv, Rat.abs_mul, Rat.abs_inv]

theorem Rat.abs_add_le (x y : Rat) : (x + y).abs ≤ x.abs + y.abs := by
  cnsimp only [Rat.abs_le]
  constructor
  · apply add_le_add
    · exact Rat.le_abs_self x
    · exact Rat.le_abs_self y
  · cnsimp only [neg_add_rev, add_comm (-y)]
    apply add_le_add
    · exact Rat.neg_le_abs_self x
    · exact Rat.neg_le_abs_self y
