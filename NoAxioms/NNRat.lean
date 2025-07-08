import NoAxioms.IntNatInstances

structure NNRat where
  num : Nat
  den : Nat
  den_nz : den ~!= 0 := by change _ ≠ _; decide

theorem NNRat.den_pos (x : NNRat) : 0 < x.den := Nat.pos_of_ne_zero x.den_nz

@[cnsimp]
theorem NNRat.den_eq_zero_iff (x : NNRat) : x.den ~= 0 ↔ False := iff_false_intro x.den_nz

instance : Eqv NNRat where
  eqv a b := a.num * b.den = b.num * a.den
  refl _ := rfl
  symm h := h.symm
  trans {a b c} h h' := by
    dsimp only at h h' ⊢
    apply Nat.mul_left_cancel' b.den_pos
    rw [← Nat.mul_assoc', Nat.mul_comm b.den, h, Nat.mul_assoc', Nat.mul_comm a.den,
      ← Nat.mul_assoc', h', Nat.mul_comm c.num, Nat.mul_assoc']

theorem NNRat.eqv_iff {x y : NNRat} : x ~= y ↔ x.num * y.den ~= y.num * x.den := Iff.rfl

instance (x y : NNRat) : Decidable (x ~= y) := inferInstanceAs (Decidable (_ = _))

protected def NNRat.ofNat (n : Nat) : NNRat := NNRat.mk n 1

instance : NatCast NNRat := ⟨NNRat.ofNat⟩
instance : OfNat NNRat n := ⟨NNRat.ofNat n⟩

@[cnsimp] theorem NNRat.num_ofNat (n : Nat) : (no_index (OfNat.ofNat n) : NNRat).num ~= OfNat.ofNat n := rfl
@[cnsimp] theorem NNRat.den_ofNat (n : Nat) : (no_index (OfNat.ofNat n) : NNRat).den ~= 1 := rfl

@[cnsimp] theorem NNRat.num_natCast (n : Nat) : (n : NNRat).num ~= n := rfl
@[cnsimp] theorem NNRat.den_natCast (n : Nat) : (n : NNRat).den ~= 1 := rfl

theorem NNRat.num_eq_zero_iff {x : NNRat} : x.num ~= 0 ↔ x ~= 0 := by
  cnsimp [eqv_iff]

def NNRat.add (x y : NNRat) : NNRat :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, mul_ne_zero x.den_nz y.den_nz⟩

protected theorem NNRat.add_congr {x₁ x₂ y₁ y₂ : NNRat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.add y₁ ~= x₂.add y₂ := by
  cnsimp only [NNRat.eqv_iff] at hx hy ⊢
  dsimp only [NNRat.add]
  cnsimp only [add_mul, ← mul_assoc]
  cnrw [mul_right_comm x₁.num, hx, mul_right_comm _ y₂.den, add_right_inj]
  cnrw [mul_right_comm _ _ y₂.den, mul_right_comm _ _ y₁.den]
  cnrw [mul_right_comm y₁.num, hy, mul_right_comm _ x₂.den]

instance : Add NNRat := ⟨NNRat.add⟩
instance : AddCongr NNRat where add_congr := NNRat.add_congr

@[cnsimp] theorem NNRat.num_add (x y : NNRat) : (x + y).num ~= x.num * y.den + y.num * x.den := rfl
@[cnsimp] theorem NNRat.den_add (x y : NNRat) : (x + y).den ~= x.den * y.den := rfl

protected theorem NNRat.add_zero (x : NNRat) : x + 0 ~= x := by
  cnsimp [eqv_iff]

protected theorem NNRat.zero_add (x : NNRat) : 0 + x ~= x := by
  cnsimp [eqv_iff]

protected theorem NNRat.add_assoc (x y z : NNRat) : x + y + z ~= x + (y + z) := by
  cnsimp only [eqv_iff, num_add, den_add]
  cnsimp only [add_mul, ← mul_assoc, add_assoc, add_right_inj]
  cnrw [mul_right_comm y.num x.den, mul_right_comm z.num x.den]

protected theorem NNRat.add_comm (x y : NNRat) : x + y ~= y + x := by
  cnsimp only [eqv_iff, num_add, den_add]
  cnsimp only [add_mul, ← mul_assoc]
  rw [Nat.add_comm]
  cnrw [mul_right_comm (_ * _) y.den x.den]

protected theorem NNRat.add_right_cancel (x y z : NNRat) (h : x + z ~= y + z) : x ~= y := by
  cnsimp only [eqv_iff, num_add, den_add] at h ⊢
  cnsimp only [← mul_assoc, add_mul, mul_right_comm z.num x.den, add_left_inj] at h
  cnsimp only [mul_right_comm _ z.den] at h
  cnsimpa only [mul_right_cancel_iff z.den_nz] using h

protected theorem NNRat.add_left_cancel (x y z : NNRat) (h : x + y ~= x + z) : y ~= z := by
  cnrw [NNRat.add_comm] at h
  exact NNRat.add_right_cancel _ _ _ h

protected theorem NNRat.natCast_succ (x : Nat) : (x.succ : NNRat) ~= (x : NNRat) + 1 := by
  cnsimp [eqv_iff]

def NNRat.mul (x y : NNRat) : NNRat :=
  ⟨x.num * y.num, x.den * y.den, mul_ne_zero x.den_nz y.den_nz⟩

theorem NNRat.mul_congr {x₁ x₂ y₁ y₂ : NNRat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.mul y₁ ~= x₂.mul y₂ := by
  cnsimp only [NNRat.eqv_iff] at hx hy ⊢
  dsimp only [NNRat.mul]
  cnsimp only [← mul_assoc]
  cnrw [mul_right_comm x₁.num, hx, mul_assoc (x₂.num * _), hy, ← mul_assoc, mul_right_comm x₂.num y₂.num]

instance : Mul NNRat := ⟨NNRat.mul⟩
instance : MulCongr NNRat where mul_congr := NNRat.mul_congr

@[cnsimp] theorem NNRat.num_mul (x y : NNRat) : (x * y).num ~= x.num * y.num := rfl
@[cnsimp] theorem NNRat.den_mul (x y : NNRat) : (x * y).den ~= x.den * y.den := rfl

protected theorem NNRat.mul_one (x : NNRat) : x * 1 ~= x := by
  cnsimp [eqv_iff]

protected theorem NNRat.one_mul (x : NNRat) : 1 * x ~= x := by
  cnsimp [eqv_iff]

protected theorem NNRat.mul_zero (x : NNRat) : x * 0 ~= 0 := by
  cnsimp [eqv_iff]

protected theorem NNRat.zero_mul (x : NNRat) : 0 * x ~= 0 := by
  cnsimp [eqv_iff]

protected theorem NNRat.mul_assoc (x y z : NNRat) : x * y * z ~= x * (y * z) := by
  cnsimp [NNRat.eqv_iff, mul_assoc]

protected theorem NNRat.mul_comm (x y : NNRat) : x * y ~= y * x := by
  cnsimp [NNRat.eqv_iff]
  cnrw [mul_comm x.num, mul_comm y.den]

protected theorem NNRat.mul_right_cancel (x y z : NNRat) (hz : z ~!= 0) (h : x * z ~= y * z) : x ~= y := by
  cnsimp only [eqv_iff, num_mul, den_mul] at h ⊢
  cnsimp only [← mul_assoc, mul_right_cancel_iff z.den_nz] at h
  cnsimp only [mul_right_comm _ z.num] at h
  cnsimpa only [mul_right_cancel_iff (num_eq_zero_iff.not.mpr hz)] using h

protected theorem NNRat.mul_left_cancel (x y z : NNRat) (hx : x ~!= 0) (h : x * y ~= x * z) : y ~= z := by
  cnrw [NNRat.mul_comm] at h
  exact NNRat.mul_right_cancel _ _ _ hx h

protected theorem NNRat.mul_add (x y z : NNRat) : x * (y + z) ~= x * y + x * z := by
  cnsimp only [eqv_iff, num_mul, num_add, den_add, den_mul]
  cnsimp only [← mul_assoc, mul_right_comm _ y.den x.den, mul_right_cancel_iff (_ : NNRat).den_nz]
  cnsimp only [mul_add, ← mul_assoc, add_mul]
  cnrw [mul_right_comm _ z.den, mul_right_comm _ y.den]

protected theorem NNRat.add_mul (x y z : NNRat) : (x + y) * z ~= x * z + y * z := by
  cnsimp [NNRat.mul_comm _ z, NNRat.mul_add]

def NNRat.inv (x : NNRat) : NNRat :=
  if h : x.num = 0 then 0
  else ⟨x.den, x.num, h⟩

theorem NNRat.inv_congr {x₁ x₂ : NNRat} (hx : x₁ ~= x₂) : x₁.inv ~= x₂.inv := by
  cnsimp only [NNRat.eqv_iff] at hx ⊢
  dsimp only [NNRat.inv]
  split
  · rename_i h'
    change x₁.num ~= 0 at h'
    cnsimp only [h', zero_mul, zero_eq_mul, den_eq_zero_iff, or'_false] at hx
    rw [hx]
    rfl
  · have h' : x₂.num ~!= 0 := by
      intro h
      apply ‹¬_›
      cnsimpa [h] using hx
    rw [dif_neg (show x₂.num ≠ 0 from h')]
    dsimp
    cnrw [mul_comm, hx]

theorem NNRat.inv_mul_cancel (x : NNRat) (hx : x ~!= 0) : x.inv * x ~= 1 := by
  dsimp only [inv]
  rw [dif_neg (show x.num ≠ 0 from num_eq_zero_iff.not.mpr hx)]
  cnsimp only [eqv_iff, num_mul, den_ofNat, mul_one, num_ofNat, den_mul, one_mul]
  cnrw [mul_comm x.den]

instance : Inv NNRat := ⟨NNRat.inv⟩
instance : InvCongr NNRat := ⟨NNRat.inv_congr⟩

protected def NNRat.div (x y : NNRat) : NNRat := x * y⁻¹

theorem NNRat.div_congr {x₁ x₂ y₁ y₂ : NNRat} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.div y₁ ~= x₂.div y₂ := by
  dsimp [NNRat.div]
  ccongr <;> assumption

instance : Div NNRat := ⟨NNRat.div⟩
instance : DivCongr NNRat where div_congr := NNRat.div_congr

instance : Semifield NNRat where
  mul_one := NNRat.mul_one
  one_mul := NNRat.one_mul
  mul_assoc := NNRat.mul_assoc
  mul_zero := NNRat.mul_zero
  zero_mul := NNRat.zero_mul
  add_zero := NNRat.add_zero
  zero_add := NNRat.zero_add
  add_assoc := NNRat.add_assoc
  add_comm := NNRat.add_comm
  natCast_zero := rfl
  natCast_succ := NNRat.natCast_succ
  mul_add := NNRat.mul_add
  add_mul := NNRat.add_mul
  mul_comm := NNRat.mul_comm
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := .intro 0 (.intro 1 (by decide))
  inv_zero := rfl
  inv_mul_cancel := NNRat.inv_mul_cancel

instance : IsCancelAdd NNRat where
  add_left_cancel := NNRat.add_left_cancel
  add_right_cancel := NNRat.add_right_cancel

instance : IsCancelMulWithZero NNRat where
  mul_left_cancel := NNRat.mul_left_cancel
  mul_right_cancel := NNRat.mul_right_cancel
