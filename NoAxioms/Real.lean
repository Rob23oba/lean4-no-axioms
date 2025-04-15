import NoAxioms.PreReal

def Real := Noncomputable PreReal
def Real.mk (x : PreReal) : Real := Noncomputable.mk x

instance : Eqv Real := inferInstanceAs (Eqv (Noncomputable PreReal))
instance : OfNat Real n := ⟨.mk (.ofRat n)⟩

@[ccongr]
theorem Real.mk_congr {x₁ x₂ : PreReal} (hx : x₁ ~= x₂) : mk x₁ ~= mk x₂ :=
  Noncomputable.mk_congr hx

theorem Real.elim {p : Prop} [DNE p] (t : Real) (h : (a : PreReal) → t ~= mk a → p) : p :=
  Noncomputable.elim t h

def Real.uniqueChoice (p : Real ~> Prop') (h : ∃' x, p x ∧ ∀ y, p y → x ~= y) : Real :=
  Noncomputable.uniqueChoice' p h

instance : Add Real where
  add x y :=
    x.bind fun' a =>
    y.bind fun' b =>
      .mk (a.add b)

@[ccongr]
theorem Real.add_congr {x₁ x₂ y₁ y₂ : Real} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ + y₁ ~= x₂ + y₂ := by
  dsimp [· + ·, Add.add, mk] at *
  ccongr <;> assumption

@[cnsimp]
theorem Real.mk_add_mk (x y : PreReal) :
    (.mk x : Real) + (.mk y : Real) ~= (.mk (x.add y)) := by
  dsimp [· + ·, Add.add, mk]
  cnsimp

theorem Real.add_comm (x y : Real) : x + y ~= y + x := by
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  cnsimp [ha, hb, PreReal.add_comm a]

theorem Real.add_assoc (x y z : Real) : x + y + z ~= x + (y + z) := by
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  refine z.elim fun c hc => ?_
  cnsimp [ha, hb, hc, PreReal.add_assoc]

@[cnsimp]
theorem Real.add_zero (x : Real) : x + 0 ~= x := by
  refine x.elim fun a ha => ?_
  change x + mk 0 ~= x
  cnsimp [ha, PreReal.add_zero]

@[cnsimp]
theorem Real.zero_add (x : Real) : 0 + x ~= x := by
  cnsimp only [Real.add_comm 0, Real.add_zero, eq'_self_iff]

instance : Neg Real where
  neg x := x.map fun' a => a.neg

@[ccongr]
theorem Real.neg_congr {x₁ x₂ : Real} (hx : x₁ ~= x₂) :
    -x₁ ~= -x₂ := by
  dsimp [Neg.neg]
  cnsimp [hx]

@[cnsimp]
theorem Real.neg_mk (x : PreReal) : -mk x ~= mk x.neg := by
  dsimp [Neg.neg, mk]
  cnsimp

@[cnsimp] theorem Real.mk_zero : mk 0 ~= 0 := by rfl
@[cnsimp] theorem Real.mk_one : mk 1 ~= 1 := by rfl

@[cnsimp]
theorem Real.add_neg (x : Real) : x + -x ~= 0 := by
  refine x.elim fun a ha => ?_
  cnsimp [ha, PreReal.add_neg]

@[cnsimp]
theorem Real.neg_zero : -0 ~= (0 : Real) := by
  calc
    (-0 : Real) ~= 0 + -0 := by cnsimp only [Real.zero_add, eq'_self_iff]
    _ ~= 0 := by cnsimp only [Real.add_neg, eq'_self_iff]

instance : Sub Real where
  sub x y := x + -y

@[ccongr]
theorem Real.sub_congr {x₁ x₂ y₁ y₂ : Real} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ - y₁ ~= x₂ - y₂ := by
  dsimp [· - ·, Sub.sub] at *
  ccongr <;> assumption

theorem Real.sub_eq'_add_neg (x y : Real) : x - y ~= x + -y := .rfl

@[cnsimp]
theorem Real.sub_zero (x : Real) : x - 0 ~= x := by
  cnsimp only [Real.sub_eq'_add_neg, Real.neg_zero, Real.add_zero, eq'_self_iff]

@[cnsimp]
theorem Real.sub_self (x : Real) : x - x ~= 0 := by
  cnsimp only [Real.sub_eq'_add_neg, Real.add_neg, eq'_self_iff]

instance : LT Real where
  lt x y := (y - x).test fun' a => a.pos

instance : LE Real where
  le x y := ¬y < x

instance (x y : Real) : DNE (x < y) := inferInstanceAs (DNE (Prop'.p _))
instance (x y : Real) : DNE (x ≤ y) := inferInstanceAs (DNE (¬ _))

@[ccongr]
theorem Real.lt_congr {x₁ x₂ y₁ y₂ : Real} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ < y₁ ↔ x₂ < y₂ := by
  dsimp only [· < ·]
  ccongr <;> assumption

@[ccongr]
theorem Real.le_congr {x₁ x₂ y₁ y₂ : Real} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ ≤ y₁ ↔ x₂ ≤ y₂ := by
  dsimp only [· ≤ ·]
  ccongr <;> assumption

theorem Real.lt_irrefl (x : Real) : ¬x < x := by
  dsimp only [· < ·]
  cnsimp only [Real.sub_self]
  change ¬Noncomputable.test (.mk 0) _
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun']
  exact PreReal.not_zero_pos

theorem Real.lt_trans {x y z : Real} (h : x < y) (h' : y < z) : x < z := by
  dsimp only [· < ·] at *
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  refine z.elim fun c hc => ?_
  cnsimp only [ha, hb, hc, Real.sub_eq'_add_neg, Real.neg_mk, Real.mk_add_mk] at h h' ⊢
  dsimp only [mk] at h h' ⊢
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun'] at h h' ⊢
  have := PreReal.add_pos h h'
  cnsimp only [PreReal.add_comm c, ← PreReal.add_assoc] at this
  cnsimp only [PreReal.add_assoc b a.neg, PreReal.add_comm a.neg] at this
  cnsimp only [← PreReal.add_assoc b b.neg, PreReal.add_neg] at this
  cnsimp only [PreReal.add_comm 0, PreReal.add_zero] at this
  cnsimp only [PreReal.add_comm a.neg] at this
  exact this

theorem Real.lt_asymm {x y : Real} (h : x < y) : ¬y < x := by
  dsimp only [· < ·] at *
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  cnsimp only [ha, hb, Real.sub_eq'_add_neg, Real.neg_mk, Real.mk_add_mk] at h ⊢
  dsimp only [mk] at h ⊢
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun'] at h ⊢
  intro h'
  have := PreReal.add_pos h h'
  cnsimp only [← PreReal.add_assoc] at this
  cnsimp only [PreReal.add_assoc b a.neg, PreReal.add_comm a.neg] at this
  cnsimp only [PreReal.add_neg, PreReal.add_zero] at this
  exact PreReal.not_zero_pos this

theorem Real.le_iff_lt_or'_eq' {x y : Real} : x ≤ y ↔ x < y ∨' x ~= y := by
  dsimp only [· < ·, · ≤ ·]
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  cnsimp only [ha, hb, Real.sub_eq'_add_neg, Real.neg_mk, Real.mk_add_mk]
  dsimp only [mk, Real]
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun', Noncomputable.mk_inj]
  have := PreReal.pos_trichotomy (a.add b.neg)
  have asubbneg : (a.add b.neg).neg ~= b.add a.neg := by
    cnsimp only [PreReal.neg_add, PreReal.neg_neg, eq'_self_iff]
  refine this.elim (fun h => ?_) (fun h => h.elim (fun h => ?_) (fun h => ?_))
  · replace h := PreReal.eq'_of_sub_eq'_zero h
    cnsimp only [h, eq'_self_iff, or'_true, iff_true_iff, PreReal.add_neg]
    cnsimp only [iff_true_intro PreReal.not_zero_pos]
  · cnsimp only [h, true_or', not_true, false_iff_iff, not_or']
    constructor
    · intro h'
      have := PreReal.add_pos h h'
      cnsimp only [← PreReal.add_assoc] at this
      cnsimp only [PreReal.add_assoc a b.neg, PreReal.add_comm b.neg] at this
      cnsimp only [PreReal.add_neg, PreReal.add_zero] at this
      exact PreReal.not_zero_pos this
    · intro h'
      cnsimp only [h', PreReal.add_neg] at h
      exact PreReal.not_zero_pos h
  · cnsimp only [asubbneg] at h
    cnsimp only [h, true_or', iff_true_iff]
    intro h'
    have := PreReal.add_pos h h'
    cnsimp only [← PreReal.add_assoc] at this
    cnsimp only [PreReal.add_assoc b a.neg, PreReal.add_comm a.neg] at this
    cnsimp only [PreReal.add_neg, PreReal.add_zero] at this
    exact PreReal.not_zero_pos this

theorem Real.le_refl (x : Real) : x ≤ x :=
  Real.lt_irrefl x

theorem Real.le_trans {x y z : Real} (h : x ≤ y) (h' : y ≤ z) : x ≤ z := by
  cnsimp only [Real.le_iff_lt_or'_eq'] at h h' ⊢
  refine h.elim (fun h => ?_) (fun h => ?_)
  · refine h'.elim (fun h' => ?_) (fun h' => ?_)
    · exact .inl (Real.lt_trans h h')
    · cnsimp only [h'] at h
      exact .inl h
  · refine h'.elim (fun h' => ?_) (fun h' => ?_)
    · cnsimp only [← h] at h'
      exact .inl h'
    · cnsimp only [h'] at h
      exact .inr h

theorem Real.le_antisymm {x y : Real} (h : x ≤ y) (h' : y ≤ x) : x ~= y := by
  cnsimp only [Real.le_iff_lt_or'_eq'] at h h'
  refine h.elim (fun h => ?_) (fun h => h)
  refine h'.elim (fun h' => ?_) (fun h' => h'.symm)
  exact (Real.lt_asymm h h').elim

theorem Real.add_lt_add_right {x y z : Real} (h : x < y) : x + z < y + z := by
  dsimp only [· < ·] at h ⊢
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  refine z.elim fun c hc => ?_
  cnsimp only [ha, hb, hc, Real.sub_eq'_add_neg, Real.neg_mk, Real.mk_add_mk] at h ⊢
  dsimp only [mk] at h ⊢
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun'] at h ⊢
  cnsimp only [PreReal.neg_add]
  have : (b.add c).add (c.neg.add a.neg) ~= b.add a.neg := by
    calc
      _ ~= (b.add (c.add c.neg)).add a.neg := by
        cnsimp only [PreReal.add_assoc, eq'_self_iff]
      _ ~= b.add a.neg := by
        cnsimp only [PreReal.add_neg, PreReal.add_zero, eq'_self_iff]
  cnsimp only [this]
  exact h

theorem Real.add_lt_add_iff_right {x y z : Real} : x + z < y + z ↔ x < y := by
  constructor
  · intro h
    have : x + z + -z < y + z + -z := Real.add_lt_add_right h
    cnsimp only [Real.add_assoc, Real.add_neg, Real.add_zero] at this
    exact this
  · exact Real.add_lt_add_right

theorem Real.add_le_add_right {x y z : Real} (h : x ≤ y) : x + z ≤ y + z := by
  dsimp only [· ≤ ·] at *
  cnsimp only [Real.add_lt_add_iff_right]
  exact h

instance : Mul Real where
  mul x y :=
    x.bind fun' a =>
    y.bind fun' b =>
      .mk (a.mul b)

@[ccongr]
theorem Real.mul_congr {x₁ x₂ y₁ y₂ : Real} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ * y₁ ~= x₂ * y₂ := by
  dsimp [· * ·, Mul.mul, mk] at *
  ccongr <;> assumption

@[cnsimp]
theorem Real.mk_mul_mk (x y : PreReal) : mk x * mk y ~= mk (x.mul y) := by
  dsimp [· * ·, Mul.mul, mk] at *
  cnsimp

@[cnsimp]
theorem Real.mul_zero (x : Real) : x * 0 ~= 0 := by
  refine x.elim fun a ha => ?_
  change _ * mk 0 ~= mk 0
  cnsimp only [ha, Real.mk_mul_mk, PreReal.mul_zero, eq'_self_iff]

@[cnsimp]
theorem Real.mul_one (x : Real) : x * 1 ~= x := by
  refine x.elim fun a ha => ?_
  change _ * mk 1 ~= x
  cnsimp only [ha, Real.mk_mul_mk, PreReal.mul_one, eq'_self_iff]

theorem Real.mul_comm (x y : Real) : x * y ~= y * x := by
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  cnsimp [ha, hb, PreReal.mul_comm a]

theorem Real.mul_assoc (x y z : Real) : x * y * z ~= x * (y * z) := by
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  refine z.elim fun c hc => ?_
  cnsimp [ha, hb, hc, PreReal.mul_assoc]

@[cnsimp]
theorem Real.zero_mul (x : Real) : 0 * x ~= 0 := by
  cnsimp only [Real.mul_comm 0, Real.mul_zero, eq'_self_iff]

@[cnsimp]
theorem Real.one_mul (x : Real) : 1 * x ~= x := by
  cnsimp only [Real.mul_comm 1, Real.mul_one, eq'_self_iff]

theorem Real.mul_add (x y z : Real) : x * (y + z) ~= x * y + x * z := by
  refine x.elim fun a ha => ?_
  refine y.elim fun b hb => ?_
  refine z.elim fun c hc => ?_
  cnsimp [ha, hb, hc, PreReal.mul_add]

theorem Real.add_mul (x y z : Real) : (x + y) * z ~= x * z + y * z := by
  cnsimp only [(Real.mul_comm · z), Real.mul_add, eq'_self_iff]
