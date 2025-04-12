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
