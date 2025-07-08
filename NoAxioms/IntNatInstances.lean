import NoAxioms.Ring

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

theorem Nat.mul_assoc' (a b c : Nat) : a * b * c = a * (b * c) := by
  induction b with
  | zero => rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.succ_mul, Nat.mul_comm, Nat.mul_add, Nat.mul_comm, ih,
      Nat.mul_add, Nat.mul_comm a c]

theorem Nat.add_mul' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm _ c, Nat.mul_comm _ c, Nat.mul_comm _ c, Nat.mul_add]

instance : CommSemiring Nat where
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_comm := Nat.mul_comm
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
  add_mul := Nat.add_mul'

instance : AddCongr Int where
  add_congr h h' := h ▸ h' ▸ rfl

instance : SubCongr Int where
  sub_congr h h' := h ▸ h' ▸ rfl

instance : MulCongr Int where
  mul_congr h h' := h ▸ h' ▸ rfl

instance : DivCongr Int where
  div_congr h h' := h ▸ h' ▸ rfl

instance : NegCongr Int where
  neg_congr h := h ▸ rfl

instance : LECongr Int where
  le_congr h h' := h ▸ h' ▸ .rfl

instance : LTCongr Int where
  lt_congr h h' := h ▸ h' ▸ .rfl

theorem Nat.add_sub_cancel_right' (a b : Nat) : a + b - b = a := by
  induction b with
  | zero => rfl
  | succ k ih =>
    dsimp only [Nat.add_succ, Nat.add_zero]
    rw [Nat.succ_sub_succ, ih]

theorem Nat.add_sub_cancel_left' (a b : Nat) : a + b - a = b := by
  rw [Nat.add_comm, Nat.add_sub_cancel_right']

theorem Nat.add_sub_cancel'' {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  rcases Nat.le.dest h with ⟨c, rfl⟩
  rw [Nat.add_sub_cancel_left']

theorem Nat.sub_add_cancel' {a b : Nat} (h : b ≤ a) : a - b + b = a := by
  rw [Nat.add_comm, Nat.add_sub_cancel'' h]

theorem Nat.sub_self_add' (a b : Nat) : a - (a + b) = 0 := by
  induction b with
  | zero => exact Nat.sub_self a
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ, ih, Nat.pred_zero]

theorem Nat.sub_eq_zero_of_le' {a b : Nat} (h : a ≤ b) : a - b = 0 := by
  rcases Nat.le.dest h with ⟨c, rfl⟩
  exact Nat.sub_self_add' a c

theorem Nat.add_right_cancel' {a b c : Nat} (h : a + c = b + c) : a = b := by
  rw [← Nat.add_sub_cancel_right' a c, h, Nat.add_sub_cancel_right' b c]

theorem Nat.add_left_cancel' {a b c : Nat} (h : a + b = a + c) : b = c := by
  rw [← Nat.add_sub_cancel_left' a b, h, Nat.add_sub_cancel_left' a c]

theorem Nat.add_right_cancel_iff' {a b c : Nat} : a + c = b + c ↔ a = b :=
  ⟨Nat.add_right_cancel', fun h => h ▸ rfl⟩

theorem Nat.add_left_cancel_iff' {a b c : Nat} : a + b = a + c ↔ b = c :=
  ⟨Nat.add_left_cancel', fun h => h ▸ rfl⟩

theorem Int.subNatNat_of_le' {a b : Nat} (h : b ≤ a) : subNatNat a b = (a - b : Nat) := by
  dsimp only [subNatNat]
  rw [Nat.sub_eq_zero_of_le' h]
  rfl

theorem Int.subNatNat_of_lt' {a b : Nat} (h : a < b) : subNatNat a b = .negSucc (b - a - 1) := by
  dsimp only [subNatNat]
  rcases Nat.le.dest h with ⟨c, rfl⟩
  rw [Nat.succ_add, ← Nat.add_succ, Nat.add_sub_cancel_left']
  rfl

theorem Int.subNatNat_add_left' (a b : Nat) : subNatNat (a + b) a = b := by
  rw [subNatNat, Nat.sub_self_add', Nat.add_sub_cancel_left', ofNat_eq_coe]

theorem Int.subNatNat_add_right' (a b : Nat) : subNatNat a (a + b + 1) = .negSucc b := by
  rw [subNatNat, Nat.add_assoc, Nat.add_sub_cancel_left']

theorem Int.subNatNat_add_right'' (a b : Nat) : subNatNat a (a + b) = -b :=
  match b with
  | 0 => Int.subNatNat_add_left' a 0
  | b' + 1 => Int.subNatNat_add_right' a b'

@[elab_as_elim]
theorem Int.subNatNat_ind {motive : Nat → Nat → Int → Prop}
    (ofNat : ∀ a b, motive (a + b) a b)
    (negSucc : ∀ a b, motive a (a + b + 1) (.negSucc b))
    (a b : Nat) : motive a b (Int.subNatNat a b) := by
  by_cases h : b ≤ a
  · have := ofNat b (a - b)
    rw [Nat.add_sub_cancel'' h] at this
    rwa [subNatNat_of_le' h]
  · replace h := Nat.not_le.mp h
    have := negSucc a (b - a - 1)
    rcases Nat.le.dest h with ⟨c, rfl⟩
    dsimp [subNatNat]
    rwa [Nat.succ_add, ← Nat.add_succ, Nat.add_sub_cancel_left'] at this ⊢

@[elab_as_elim]
theorem Int.subNatNat_ind' {motive : Int → Prop}
    (subNatNat : ∀ a b, motive (subNatNat a b))
    (t : Int) : motive t := by
  rcases t with (t | t)
  · refine cast (congrArg motive ?_) (subNatNat t 0)
    dsimp only [Int.subNatNat]
    rw [Nat.zero_sub, Nat.sub_zero]
  · exact subNatNat 0 (t + 1)

theorem Int.subNatNat_add_add_left (a b c : Nat) :
    subNatNat (a + b) (a + c) = subNatNat b c := by
  refine subNatNat_ind (fun b c => ?_) (fun b c => ?_) b c
  · rw [← Nat.add_assoc, Int.subNatNat_add_left']
  · rw [← Nat.add_assoc, ← Nat.add_assoc, Int.subNatNat_add_right']

theorem Int.negSucc_inj' {a b : Nat} : Int.negSucc a = .negSucc b ↔ a = b :=
  ⟨Int.negSucc.inj, fun h => h ▸ rfl⟩

theorem Nat.succ_inj'' {a b : Nat} : a.succ = b.succ ↔ a = b :=
  ⟨Nat.succ.inj, fun h => h ▸ rfl⟩

theorem Int.subNatNat_eq_subNatNat {a b c d : Nat} :
    subNatNat a b = subNatNat c d ↔ a + d = c + b := by
  refine subNatNat_ind (fun a b => ?_) (fun a b => ?_) a b
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · refine Int.ofNat_inj.trans ?_
      rw [Nat.add_right_comm, Nat.add_comm _ a, ← Nat.add_assoc]
      exact Nat.add_left_cancel_iff'.symm
    · rw [Nat.add_assoc c, Nat.add_left_comm, ← Nat.add_assoc c, ← Nat.add_assoc c,
        Nat.add_assoc]
      refine Iff.trans ?_ (Nat.add_left_cancel_iff' (c := 0)).symm
      exact iff_of_false Int.noConfusion Nat.noConfusion
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · rw [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm d, ← Nat.add_assoc,
        ← Nat.add_assoc, ← Nat.add_assoc, Nat.add_assoc (c + a), Nat.add_assoc (c + a)]
      refine Iff.trans ?_ (Nat.add_left_cancel_iff' (b := 0)).symm
      exact iff_of_false Int.noConfusion Nat.noConfusion
    · refine Int.negSucc_inj'.trans ?_
      rw [Nat.add_assoc c, Nat.add_left_comm, ← Nat.add_assoc c, ← Nat.add_assoc c,
        ← Nat.add_assoc c, Nat.add_assoc (c + a)]
      refine Iff.trans ?_ Nat.add_left_cancel_iff'.symm
      exact eq_comm.trans Nat.succ_inj''.symm

theorem Int.subNatNat_add_subNatNat (a b c d : Nat) :
    subNatNat a b + subNatNat c d = subNatNat (a + c) (b + d) := by
  refine subNatNat_ind (fun a b => ?_) (fun a b => ?_) a b
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · rw [Nat.add_assoc, Nat.add_left_comm b, ← Nat.add_assoc, Int.subNatNat_add_left',
        Int.natCast_add]
    · rw [Int.ofNat_add_negSucc, ← Nat.add_assoc, ← Nat.add_assoc,
        Nat.add_right_comm, Nat.add_assoc (a + c), Int.subNatNat_add_add_left]
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · rw [Int.negSucc_add_ofNat, ← Nat.add_assoc, Nat.add_right_comm _ 1,
        Nat.add_right_comm a b, Nat.add_assoc (a + c), subNatNat_add_add_left]
    · rw [Int.negSucc_add_negSucc, Nat.succ_add, Nat.add_assoc, Nat.add_assoc,
        Nat.add_left_comm b, ← Nat.add_assoc, subNatNat_add_right', Nat.add_succ]

theorem Int.add_comm' (a b : Int) : a + b = b + a := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  induction b using Int.subNatNat_ind' with | subNatNat x' y' => ?_
  rw [Int.subNatNat_add_subNatNat, Int.subNatNat_add_subNatNat,
    Nat.add_comm x, Nat.add_comm y]

theorem Int.add_assoc' (a b c : Int) : a + b + c = a + (b + c) := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  induction b using Int.subNatNat_ind' with | subNatNat x' y' => ?_
  induction c using Int.subNatNat_ind' with | subNatNat x'' y'' => ?_
  repeat rw [Int.subNatNat_add_subNatNat]
  rw [Nat.add_assoc, Nat.add_assoc]

theorem Int.zero_add' (a : Int) : 0 + a = a := by
  rw [Int.add_comm', Int.add_zero]

theorem Int.neg_subNatNat (a b : Nat) : -subNatNat a b = subNatNat b a := by
  refine subNatNat_ind (fun a b => ?_) (fun a b => ?_) a b
  · rw [subNatNat_add_right'']
  · rw [neg_negSucc, Nat.add_assoc, subNatNat_add_left']

theorem Int.neg_add_cancel (a : Int) : -a + a = 0 := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  rw [Int.neg_subNatNat, Int.subNatNat_add_subNatNat, Nat.add_comm]
  exact subNatNat_add_left' _ 0

theorem Int.subNatNat_mul_subNatNat (a b c d : Nat) :
    subNatNat a b * subNatNat c d = subNatNat (a * c + b * d) (b * c + a * d) := by
  refine subNatNat_ind (fun a b => ?_) (fun a b => ?_) a b
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · rw [Nat.add_mul', Nat.mul_add b, Nat.add_mul', Nat.add_right_comm,
        ← Nat.add_assoc, ← Nat.add_assoc, Int.subNatNat_add_left', natCast_mul]
    · rw [ofNat_mul_negSucc, Nat.add_mul', Nat.add_mul', Nat.add_right_comm,
        Nat.add_assoc c, Nat.mul_add b, ← Nat.add_assoc, ← Nat.add_assoc,
        ← Nat.add_assoc, Int.subNatNat_add_right'']
  · refine subNatNat_ind (fun c d => ?_) (fun c d => ?_) c d
    · rw [negSucc_mul_ofNat, Nat.add_comm, Nat.add_assoc, Nat.mul_add,
        Nat.mul_add, Nat.add_mul' _ _ d, Nat.add_right_comm, ← Nat.add_assoc,
        ← Nat.add_assoc _ (a * d), Int.subNatNat_add_right'']
    · rw [Nat.add_assoc c, Nat.mul_add, Nat.add_assoc a,
        Nat.add_mul' _ _ (d + 1), Nat.mul_add a c, Nat.add_left_comm,
        ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc (_ * _),
        Int.subNatNat_add_left', Int.negSucc_mul_negSucc, Int.natCast_mul]

theorem Int.mul_comm' (a b : Int) : a * b = b * a := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  induction b using Int.subNatNat_ind' with | subNatNat x' y' => ?_
  rw [Int.subNatNat_mul_subNatNat, Int.subNatNat_mul_subNatNat]
  rw [Nat.mul_comm x, Nat.mul_comm y, Nat.mul_comm x, Nat.mul_comm y,
    Nat.add_comm (x' * y)]

theorem Int.mul_assoc' (a b c : Int) : a * b * c = a * (b * c) := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  induction b using Int.subNatNat_ind' with | subNatNat x' y' => ?_
  induction c using Int.subNatNat_ind' with | subNatNat x'' y'' => ?_
  repeat rw [Int.subNatNat_mul_subNatNat]
  apply subNatNat_eq_subNatNat.mpr
  simp only [Nat.add_mul', Nat.mul_add, ← Nat.mul_assoc', ← Nat.add_assoc]
  rw [Nat.add_right_comm _ (x * x' * y'')]
  rw [Nat.add_right_comm _ (y * y' * y'')]
  rw [Nat.add_right_comm _ (y * x' * y'')]
  rw [Nat.add_right_comm _ (y * y' * x'')]

theorem Int.mul_one' (a : Int) : a * 1 = a := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  change _ * subNatNat 1 0 = _
  rw [Int.subNatNat_mul_subNatNat, Nat.mul_one, Nat.mul_one,
    Nat.mul_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero]

theorem Int.one_mul' (a : Int) : 1 * a = a := by
  rw [Int.mul_comm', Int.mul_one']

theorem Int.zero_mul' (a : Int) : 0 * a = 0 := by
  rw [Int.mul_comm', Int.mul_zero]

theorem Int.mul_add' (a b c : Int) : a * (b + c) = a * b + a * c := by
  induction a using Int.subNatNat_ind' with | subNatNat x y => ?_
  induction b using Int.subNatNat_ind' with | subNatNat x' y' => ?_
  induction c using Int.subNatNat_ind' with | subNatNat x'' y'' => ?_
  rw [Int.subNatNat_add_subNatNat, Int.subNatNat_mul_subNatNat]
  rw [Int.subNatNat_mul_subNatNat, Int.subNatNat_mul_subNatNat, Int.subNatNat_add_subNatNat]
  apply subNatNat_eq_subNatNat.mpr
  simp only [Nat.mul_add, ← Nat.add_assoc]
  rw [Nat.add_right_comm _ (x * y'), Nat.add_right_comm _ (x * x'')]

theorem Int.add_mul' (a b c : Int) : (a + b) * c = a * c + b * c := by
  rw [Int.mul_comm' _ c, Int.mul_comm' _ c, Int.mul_comm' _ c, Int.mul_add']

instance : CommRing Int where
  add_zero := Int.add_zero
  zero_add := Int.zero_add'
  add_assoc := Int.add_assoc'
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Int.neg_add_cancel
  add_comm := Int.add_comm'
  mul_one := Int.mul_one'
  one_mul := Int.one_mul'
  mul_assoc := Int.mul_assoc'
  mul_zero := Int.mul_zero
  zero_mul := Int.zero_mul'
  natCast_zero := rfl
  natCast_succ _ := rfl
  mul_add := Int.mul_add'
  add_mul := Int.add_mul'
  mul_comm := Int.mul_comm'

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

theorem Nat.mul_left_cancel' {a b c : Nat} (ha : 0 < a) (h : a * b = a * c) : b = c := by
  rw [Nat.mul_comm a, Nat.mul_comm a] at h
  exact Nat.mul_right_cancel' ha h

instance : IsCancelAdd Nat where
  add_left_cancel _ _ _ := Nat.add_left_cancel'
  add_right_cancel _ _ _ := Nat.add_right_cancel'

instance : IsCancelMulWithZero Nat where
  mul_left_cancel _ _ _ h := Nat.mul_left_cancel' (Nat.pos_of_ne_zero h)
  mul_right_cancel _ _ _ h := Nat.mul_right_cancel' (Nat.pos_of_ne_zero h)
