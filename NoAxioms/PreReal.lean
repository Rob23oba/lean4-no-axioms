import NoAxioms.Rat

structure PreReal where
  seq : Nat → Noncomputable Rat
  isCauSeq : ∀ ε > 0, ∃' i, ∀ j ≥ i,
    (seq i).test fun' a =>
    (seq j).test fun' b =>
      (b - a).abs < ε

instance : Eqv PreReal where
  eqv x y := ∀ ε > 0, ∃' i, ∀ j ≥ i,
    (x.seq j).test fun' a =>
    (y.seq j).test fun' b =>
      (b - a).abs < ε
  refl x ε hε := by
    refine .intro 0 fun j hj => ?_
    refine (x.seq j).ind fun a b hab => ?_
    cnsimp [hab]
    exact hε
  symm {x y} h ε hε := by
    specialize h ε hε
    refine h.elim fun i hi => ?_
    clear h
    refine .intro i ?_
    intro j hj
    specialize hi j hj
    refine (x.seq j).ind (fun a b hab hi => ?_) hi
    refine (y.seq j).ind (fun a' b' hab' hi => ?_) hi
    cnsimp [hab, hab'] at hi ⊢
    cnsimp [Rat.abs_sub_comm b]
    exact hi
  trans {x y z} h h' ε hε := by
    dsimp at h h'
    specialize h (ε / 2) (Rat.div_pos hε (by decide))
    specialize h' (ε / 2) (Rat.div_pos hε (by decide))
    refine h.elim fun i hi => ?_
    refine h'.elim fun i' hi' => ?_
    clear h h'
    refine .intro (max i i') ?_
    intro j hj
    dsimp [GE.ge] at hj
    cnsimp only [Nat.max_le'] at hj
    specialize hi j hj.1
    specialize hi' j hj.2
    refine (x.seq j).ind (fun a b hab hi hi' => ?_) hi hi'
    refine (y.seq j).ind (fun a' b' hab' hi hi' => ?_) hi hi'
    refine (z.seq j).ind (fun a'' b'' hab'' hi hi' => ?_) hi hi'
    cnsimp [hab, hab', hab''] at hi hi' ⊢
    have := Rat.abs_sub_lt_trans hi hi'
    cnsimp [Rat.half_add_half] at this
    exact this

theorem PreReal.eqv_def (x y : PreReal) : x ~= y ↔
    ∀ ε > 0, ∃' i, ∀ j ≥ i,
      (x.seq j).test fun' a =>
      (y.seq j).test fun' b =>
        (b - a).abs < ε := Iff.rfl

theorem PreReal.eqv_of_seq_eq {x y : PreReal} (h : ∀ i, x.seq i ~= y.seq i) :
    x ~= y := by
  cnsimp only [PreReal.eqv_def, h]
  intro ε hε
  refine .intro 0 fun j hj => ?_
  refine (y.seq j).elim (fun a ha => ?_)
  cnsimp [ha]
  assumption

def PreReal.ofRat (x : Rat) : PreReal where
  seq _ := .mk x
  isCauSeq ε hε := by
    refine .intro 0 ?_
    intro j hj
    dsimp
    cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun',
      Rat.sub_self, Rat.abs_of_nonneg (by decide : (0 : Rat) ≤ 0)]
    exact hε

instance : OfNat PreReal n := ⟨PreReal.ofRat n⟩

@[cnsimp]
theorem PreReal.seq_ofNat (n i : Nat) : seq (no_index (OfNat.ofNat n)) i ~= .mk n := by
  rfl

@[ccongr]
theorem PreReal.ofRat_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : ofRat x₁ ~= ofRat x₂ := by
  dsimp only [ofRat]
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun', Rat.sub_self,
    PreReal.eqv_def, hx, Rat.abs_ofNat]
  intro _ h
  refine .intro 0 ?_
  intro _ ?_
  exact h

theorem Nat.le_max_left' (x y : Nat) : x ≤ max x y := by
  cnsimp only [Nat.le_max']
  exact Or'.inl (Nat.le_refl _)

theorem Nat.le_max_right' (x y : Nat) : y ≤ max x y := by
  cnsimp only [Nat.le_max']
  exact Or'.inr (Nat.le_refl _)

def PreReal.add (x y : PreReal) : PreReal where
  seq i :=
    (x.seq i).bind fun' a =>
    (y.seq i).bind fun' b =>
      .mk (a + b)
  isCauSeq ε hε := by
    have h := x.isCauSeq (ε / 2 / 2) (Rat.div_pos (Rat.div_pos hε (by decide)) (by decide))
    have h' := y.isCauSeq (ε / 2 / 2) (Rat.div_pos (Rat.div_pos hε (by decide)) (by decide))
    refine h.elim fun i hi => ?_
    refine h'.elim fun i' hi' => ?_
    clear h h'
    refine .intro (max i i') fun j hj => ?_
    dsimp [GE.ge] at hj
    cnsimp only [Nat.max_le'] at hj
    have hi'' := hi (max i i') (Nat.le_max_left' ..)
    have hi''' := hi' (max i i') (Nat.le_max_right' ..)
    specialize hi j hj.1
    specialize hi' j hj.2
    dsimp
    refine (x.seq (max i i')).elim fun a₁ ha₁ => ?_
    refine (y.seq (max i i')).elim fun a₂ ha₂ => ?_
    refine (x.seq j).elim (fun a₃ ha₃ => ?_)
    refine (y.seq j).elim (fun a₄ ha₄ => ?_)
    refine (x.seq i).elim (fun a₅ ha₅ => ?_)
    refine (y.seq i').elim (fun a₆ ha₆ => ?_)
    cnsimp [ha₁, ha₂, ha₃, ha₄, ha₅, ha₆] at hi hi' hi'' hi''' ⊢
    cnsimp only [Rat.abs_sub_comm a₂] at hi'''
    have h := Rat.abs_sub_lt_trans hi''' hi'
    cnsimp only [Rat.abs_sub_comm _ a₅] at hi''
    have h' := Rat.abs_sub_lt_trans hi'' hi
    cnsimp only [Rat.half_add_half] at h h'
    have h'' := Rat.abs_add_lt h h'
    cnsimp only [Rat.half_add_half] at h''
    refine Rat.lt_of_eq'_of_lt ?_ h''
    apply Rat.abs_congr
    cnsimp [Rat.sub_eq'_add_neg, Rat.neg_add, ← Rat.add_assoc, Rat.add_right_comm _ (-a₂) a₃,
      Rat.add_comm a₃ a₄]

@[ccongr]
theorem PreReal.add_congr {x₁ x₂ y₁ y₂ : PreReal} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.add y₁ ~= x₂.add y₂ := by
  cnsimp only [eqv_def] at *
  dsimp only [PreReal.add]
  intro ε hε
  specialize hx (ε / 2) (Rat.div_pos hε (by decide))
  specialize hy (ε / 2) (Rat.div_pos hε (by decide))
  refine hx.elim fun i hi => ?_
  refine hy.elim fun i' hi' => ?_
  clear hx hy
  refine .intro (max i i') fun j hj => ?_
  dsimp only [GE.ge] at hj
  cnsimp only [Nat.max_le'] at hj
  specialize hi j hj.1
  specialize hi' j hj.2
  refine (x₁.seq j).elim (fun a₁ ha₁ => ?_)
  refine (x₂.seq j).elim (fun a₂ ha₂ => ?_)
  refine (y₁.seq j).elim (fun a₃ ha₃ => ?_)
  refine (y₂.seq j).elim (fun a₄ ha₄ => ?_)
  cnsimp [ha₁, ha₂, ha₃, ha₄] at hi hi' ⊢
  have h := Rat.abs_add_lt hi hi'
  cnsimp only [Rat.half_add_half] at h
  refine Rat.lt_of_eq'_of_lt ?_ h
  apply Rat.abs_congr
  cnsimp [Rat.sub_eq'_add_neg, Rat.neg_add, ← Rat.add_assoc, Rat.add_right_comm _ (-a₃),
    Rat.add_right_comm _ (-a₁) a₄]

theorem PreReal.add_comm (x y : PreReal) : x.add y ~= y.add x := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [add]
  refine (x.seq i).elim (fun a ha => ?_)
  refine (y.seq i).elim (fun a' ha' => ?_)
  cnsimp [ha, ha', Rat.add_comm a]

theorem PreReal.add_assoc (x y z : PreReal) : (x.add y).add z ~= x.add (y.add z) := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [add]
  refine (x.seq i).elim (fun a ha => ?_)
  refine (y.seq i).elim (fun a' ha' => ?_)
  refine (z.seq i).elim (fun a'' ha'' => ?_)
  cnsimp [ha, ha', ha'', Rat.add_assoc]

theorem PreReal.add_zero (x : PreReal) : x.add 0 ~= x := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [add]
  refine (x.seq i).elim (fun a ha => ?_)
  cnsimp [ha, Rat.add_zero, Rat.natCast_zero]

def PreReal.neg (x : PreReal) : PreReal where
  seq i := (x.seq i).map (fun' y => -y)
  isCauSeq ε hε := by
    refine (x.isCauSeq ε hε).elim fun i hi => ?_
    refine .intro i fun j hj => ?_
    specialize hi j hj
    refine (x.seq i).elim (fun a ha => ?_)
    refine (x.seq j).elim (fun a' ha' => ?_)
    dsimp
    cnsimp [ha, ha'] at hi ⊢
    cnsimp only [← Rat.abs_neg (a + -a'), Rat.sub_eq'_add_neg, Rat.neg_neg, Rat.add_comm _ a]
    cnsimp only [← Rat.sub_eq'_add_neg, Rat.neg_sub]
    exact hi

@[ccongr]
theorem PreReal.neg_congr {x₁ x₂ : PreReal} (hx : x₁ ~= x₂) : x₁.neg ~= x₂.neg := by
  cnsimp only [eqv_def] at *
  dsimp only [PreReal.neg]
  intro ε hε
  specialize hx ε hε
  refine hx.elim fun i hi => ?_
  clear hx
  refine .intro i fun j hj => ?_
  specialize hi j hj
  refine (x₁.seq j).elim (fun a ha => ?_)
  refine (x₂.seq j).elim (fun a' ha' => ?_)
  cnsimp [ha, ha'] at hi ⊢
  cnsimp only [← Rat.abs_neg (a + -a'), Rat.sub_eq'_add_neg, Rat.neg_neg, Rat.add_comm _ a]
  cnsimp only [← Rat.sub_eq'_add_neg, Rat.neg_sub]
  exact hi

theorem PreReal.add_neg (x : PreReal) : x.add x.neg ~= 0 := by
  apply PreReal.eqv_of_seq_eq fun i => ?_
  dsimp [PreReal.add, PreReal.neg]
  refine (x.seq i).elim (fun a ha => ?_)
  cnsimp [ha, Rat.natCast_zero]
