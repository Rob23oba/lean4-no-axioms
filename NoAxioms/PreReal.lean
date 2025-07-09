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
    specialize h (ε / 2) (div_pos hε (by decide))
    specialize h' (ε / 2) (div_pos hε (by decide))
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
    cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun',
      sub_self, Rat.abs_of_nonneg (by decide : (0 : Rat) ≤ 0)]
    exact hε

instance : OfNat PreReal n := ⟨PreReal.ofRat n⟩

@[cnsimp]
theorem PreReal.seq_ofNat (n i : Nat) : seq (no_index (OfNat.ofNat n)) i ~= .mk (no_index (OfNat.ofNat n)) := by
  rfl

@[ccongr]
theorem PreReal.ofRat_congr {x₁ x₂ : Rat} (hx : x₁ ~= x₂) : ofRat x₁ ~= ofRat x₂ := by
  dsimp only [ofRat]
  cnsimp only [Noncomputable.test_mk, Fun.apply_mkFun', sub_self,
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

protected def PreReal.add (x y : PreReal) : PreReal where
  seq i :=
    (x.seq i).bind fun' a =>
    (y.seq i).bind fun' b =>
      .mk (a + b)
  isCauSeq ε hε := by
    have h := x.isCauSeq (ε / 2 / 2) (div_pos (div_pos hε (by decide)) (by decide))
    have h' := y.isCauSeq (ε / 2 / 2) (div_pos (div_pos hε (by decide)) (by decide))
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
    refine lt_of_eq'_of_lt ?_ h''
    apply Rat.abs_congr
    cnsimp [sub_eq_add_neg, neg_add_rev, ← add_assoc, add_right_comm _ (-a₂) a₃,
      add_comm a₃ a₄]

@[ccongr]
protected theorem PreReal.add_congr {x₁ x₂ y₁ y₂ : PreReal} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.add y₁ ~= x₂.add y₂ := by
  cnsimp only [eqv_def] at *
  dsimp only [PreReal.add]
  intro ε hε
  specialize hx (ε / 2) (div_pos hε (by decide))
  specialize hy (ε / 2) (div_pos hε (by decide))
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
  refine lt_of_eq'_of_lt ?_ h
  apply Rat.abs_congr
  cnsimp [sub_eq_add_neg, neg_add_rev, ← add_assoc, add_right_comm _ (-a₃),
    add_right_comm _ (-a₁) a₄]

protected theorem PreReal.add_comm (x y : PreReal) : x.add y ~= y.add x := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [PreReal.add]
  refine (x.seq i).elim (fun a ha => ?_)
  refine (y.seq i).elim (fun a' ha' => ?_)
  cnsimp [ha, ha', add_comm a]

protected theorem PreReal.add_assoc (x y z : PreReal) : (x.add y).add z ~= x.add (y.add z) := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [PreReal.add]
  refine (x.seq i).elim (fun a ha => ?_)
  refine (y.seq i).elim (fun a' ha' => ?_)
  refine (z.seq i).elim (fun a'' ha'' => ?_)
  cnsimp [ha, ha', ha'', add_assoc]

protected theorem PreReal.add_zero (x : PreReal) : x.add 0 ~= x := by
  apply eqv_of_seq_eq fun i => ?_
  dsimp only [PreReal.add]
  refine (x.seq i).elim (fun a ha => ?_)
  cnsimp [ha, add_zero, Rat.natCast_zero]

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
    cnsimp only [← Rat.abs_neg (a + -a'), sub_eq_add_neg, neg_neg, add_comm _ a]
    cnsimp only [← sub_eq_add_neg, neg_sub]
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
  cnsimp only [← Rat.abs_neg (a + -a'), sub_eq_add_neg, neg_neg, add_comm _ a]
  cnsimp only [← sub_eq_add_neg, neg_sub]
  exact hi

theorem PreReal.add_neg (x : PreReal) : x.add x.neg ~= 0 := by
  apply PreReal.eqv_of_seq_eq fun i => ?_
  dsimp [PreReal.add, PreReal.neg]
  refine (x.seq i).elim (fun a ha => ?_)
  cnsimp [ha, Rat.natCast_zero]

/-- is positive? -/
def PreReal.pos (x : PreReal) : Prop :=
  ∃' ε : Rat, 0 < ε ∧ ∃' i, ∀ j ≥ i, (x.seq j).test fun' a => ε < a

instance (x : PreReal) : DNE x.pos := inferInstanceAs (DNE (∃' _, _))

theorem PreReal.pos_congr_imp {x₁ x₂ : PreReal} (hx : x₁ ~= x₂) :
    x₁.pos → x₂.pos := by
  dsimp [PreReal.pos]
  cnsimp only [eqv_def] at hx
  intro h
  refine h.elim fun ε hε => ?_
  clear h
  obtain ⟨hε, h⟩ := hε
  refine h.elim fun i hi => ?_
  clear h
  specialize hx (ε / 2) (div_pos hε (by decide))
  refine .intro (ε / 2) ⟨div_pos hε (by decide), ?_⟩
  refine hx.elim fun i' hi' => ?_
  clear hx
  refine .intro (max i i') fun j hj => ?_
  dsimp [GE.ge] at hj
  cnsimp only [Nat.max_le'] at hj
  specialize hi j hj.1
  specialize hi' j hj.2
  refine (x₁.seq j).elim fun a ha => ?_
  refine (x₂.seq j).elim fun b hb => ?_
  cnsimp [ha, hb, Rat.abs_lt, neg_sub] at hi hi' ⊢
  replace hi' := hi'.2
  cnsimp only [sub_lt_iff_lt_add] at hi'
  replace hi := hi.trans hi'
  cnsimp only [add_comm _ b] at hi
  cnsimp only [← sub_lt_iff_lt_add] at hi
  refine lt_of_eq'_of_lt ?_ hi
  calc
    ε / 2 ~= ε / 2 + ε / 2 - ε / 2 := by cnsimp only [add_sub_cancel_right, eq'_self_iff]
    _ ~= ε - ε / 2 := by cnsimp only [Rat.half_add_half, eq'_self_iff]

set_option Elab.async false

@[ccongr]
theorem PreReal.pos_congr {x₁ x₂ : PreReal} (hx : x₁ ~= x₂) :
    x₁.pos ↔ x₂.pos :=
  ⟨pos_congr_imp hx, pos_congr_imp hx.symm⟩

def PreReal.seqMax (x : PreReal) (i : Nat) : Noncomputable Rat :=
  match i with
  | 0 => x.seq 0
  | k + 1 =>
    (seqMax x k).bind fun' a =>
    (x.seq (k + 1)).map fun' b =>
    a.max b

theorem PreReal.le_seqMax (x : PreReal) (i : Nat) :
    ∀ j ≤ i, (x.seqMax i).test fun' a => (x.seq j).test fun' b => b ≤ a := by
  intro j hle
  induction i with
  | zero =>
    dsimp [seqMax]
    match j, hle with
    | 0, _ =>
      refine (x.seq 0).elim fun a ha => ?_
      cnsimp only [ha, Noncomputable.test_mk, Fun.apply_mkFun']
      exact Rat.le_refl _
  | succ k ih =>
    dsimp [seqMax]
    refine (x.seqMax k).elim fun a ha => ?_
    refine (x.seq (k + 1)).elim fun b hb => ?_
    cnsimp only [ha, hb, Noncomputable.test_mk, Noncomputable.bind_mk, Noncomputable.map_mk,
      Fun.apply_mkFun'] at ih ⊢
    generalize h : k + 1 = a at hb hle
    cases hle with
    | refl =>
      cnsimp [hb, iff_true_intro (Rat.le_max_right _ _)]
      exact trivial
    | step h' =>
      cases Nat.succ.inj h
      specialize ih h'
      refine (x.seq j).elim fun c hc => ?_
      cnsimp only [hc, Noncomputable.test_mk, Fun.apply_mkFun'] at ih ⊢
      exact Rat.le_max_of_le_left ih

theorem PreReal.exists_gt_seq (x : PreReal) :
    ∃' q : Rat, ∀ i, (x.seq i).test (fun' a => a < q) := by
  refine (x.isCauSeq 1 (by decide)).elim fun i hi => ?_
  refine (seqMax x i).elim fun a ha => ?_
  refine .intro (a + 1) ?_
  intro j
  by_cases' h : j ≤ i
  · refine (x.seq j).elim fun b hb => ?_
    have := PreReal.le_seqMax x i j h
    cnsimp [ha, hb] at this ⊢
    apply lt_of_le_of_lt this
    exact lt_add_right_of_pos (by decide)
  · replace h := Nat.le_of_not_le h
    specialize hi j h
    have := PreReal.le_seqMax x i i (Nat.le_refl _)
    refine (x.seq i).elim fun b hb => ?_
    refine (x.seq j).elim fun c hc => ?_
    cnsimp [ha, hb, hc, Rat.abs_lt, neg_sub] at hi this ⊢
    replace hi := hi.1
    cnsimp only [sub_lt_iff_lt_add, add_comm 1 b] at hi
    apply lt_of_lt_of_le hi
    apply add_le_add_right
    exact this

theorem PreReal.exists_gt_abs_seq (x : PreReal) :
    ∃' q : Rat, ∀ i, (x.seq i).test fun' a => a.abs < q := by
  refine x.exists_gt_seq.elim fun a ha => ?_
  refine x.neg.exists_gt_seq.elim fun b hb => ?_
  refine .intro (a.max b) ?_
  intro i
  dsimp [PreReal.neg] at hb
  specialize ha i
  specialize hb i
  refine (x.seq i).elim fun c hc => ?_
  cnsimp [hc, Rat.abs_lt] at ha hb ⊢
  constructor
  · exact Rat.lt_max_of_lt_left ha
  · exact Rat.lt_max_of_lt_right hb

theorem PreReal.mul_rat_cond1 {e a b : Rat}
    (he : 0 < e) (he' : e ≤ 8 * a * b) (ha : 0 < a) (hb : 0 < b) :
    e / b / 4 * (e / a / 4) + a * (e / a / 4) + e / b / 4 * b ≤ e := by
  calc
    _ ~= e * e * a⁻¹ * b⁻¹ * 16⁻¹ + e * 4⁻¹ + e * 4⁻¹ := by
      cnsimp only [div_eq_mul_inv, ← mul_assoc, mul_right_comm _ _ e,
        mul_comm a e, mul_right_comm _ 4⁻¹ b]
      cnsimp only [mul_assoc e a, mul_assoc e b⁻¹,
        mul_inv_cancel ha.ne',
        inv_mul_cancel hb.ne',
        mul_one, add_right_cancel_iff]
      cnsimp only [mul_right_comm _ 4⁻¹ a⁻¹, mul_right_comm _ b⁻¹ a⁻¹]
      cnsimp only [mul_assoc _ (4 : Rat)⁻¹]
      rfl
    _ ≤ e * 1 := by
      cnsimp only [mul_assoc e, ← Rat.mul_add]
      cnsimp only [add_assoc]
      apply mul_le_mul_of_nonneg_left _ he.le
      cnsimp only [← le_sub_iff_add_le, show (1 : Rat) - (4⁻¹ + 4⁻¹) ~= 8 * 16⁻¹ from rfl]
      cnsimp only [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by decide)
      cnsimp only [← div_eq_mul_inv]
      cnsimp only [div_le_iff hb]
      cnsimp only [div_le_iff ha]
      cnsimp only [mul_right_comm _ b, he']
    _ ~= e := by cnsimp

theorem mul_le_mul_of_abs_le_of_abs_le {a b c d : Rat}
    (h : a.abs ≤ c) (h' : b.abs ≤ d) :
    a * b ≤ c * d := by
  have : a.abs * b.abs ≤ c * d :=
    mul_le_mul h h' (Rat.abs_nonneg _) ((Rat.abs_nonneg _).trans h)
  cnsimp only [← Rat.abs_mul, Rat.abs_le] at this
  exact this.1

theorem PreReal.mul_rat_cond' {a b e x y x' y' : Rat}
    (hxy : 0 ≤ x ∧ 0 ≤ y ∨' 0 ≤ x' ∧ 0 ≤ y')
    (hapos : 0 < a) (hbpos : 0 < b)
    (hx' : x' < a) (hy' : y' < b)
    (he : e ≤ 8 * a * b) (hepos : 0 < e)
    (hxx' : (x - x').abs < e / b / 4)
    (hyy' : (y - y').abs < e / a / 4) :
    x * y - x' * y' < e := by
  replace hxx' := hxx'.le
  replace hyy' := hyy'.le
  have eadivpos : 0 < e / a / 4 :=
    div_pos (div_pos hepos hapos) (by decide)
  have ebdivpos : 0 < e / b / 4 :=
    div_pos (div_pos hepos hbpos) (by decide)
  have le1 : x * y - x' * y' ≤ e / b / 4 * (e / a / 4) + x' * (e / a / 4) + e / b / 4 * y' := by
    refine hxy.elim (fun hxy => ?_) (fun hxy => ?_)
    · obtain ⟨hx, hy⟩ := hxy
      calc
        x * y - x' * y' ~= (x - x' + x') * (y - y' + y') - x' * y' := by cnsimp
        _ ≤ (e / b / 4 + x') * (e / a / 4 + y') - x' * y' :=
          sub_le_sub_right
            (mul_le_mul_of_nonneg'
              (add_le_add_right (Rat.abs_le.mp hxx').1)
              (add_le_add_right (Rat.abs_le.mp hyy').1)
              (le_of_le_of_eq' hx (sub_add_cancel ..).symm)
              ((le_of_le_of_eq' hy (sub_add_cancel ..).symm).trans
                (add_le_add_right (Rat.abs_le.mp hyy').1)))
        _ ~= e / b / 4 * (e / a / 4) + x' * (e / a / 4) + e / b / 4 * y' := by
          cnsimp only [mul_add]
          cnsimp only [add_mul, eq'_self_iff, ← add_assoc, add_sub_cancel_right]
    · obtain ⟨hx, hy⟩ := hxy
      calc
        x * y - x' * y' ~= (x - x' + x') * (y - y' + y') - x' * y' := by cnsimp
        _ ~= (x - x') * (y - y') + x' * (y - y') + (x - x') * y' := by
          cnsimp only [mul_add]
          cnsimp only [Rat.add_mul, eq'_self_iff, ← add_assoc, add_sub_cancel_right]
        _ ≤ e / b / 4 * (e / a / 4) + x' * (e / a / 4) + e / b / 4 * y' :=
          add_le_add
            (add_le_add (mul_le_mul_of_abs_le_of_abs_le hxx' hyy')
              (mul_le_mul_of_nonneg_left (Rat.abs_le.mp hyy').1 hx))
            (mul_le_mul_of_nonneg_right (Rat.abs_le.mp hxx').1 hy)
  calc
    x * y - x' * y' ≤ _ := le1
    _ < e / b / 4 * (e / a / 4) + a * (e / a / 4) + e / b / 4 * b :=
      add_lt_add
        (add_lt_add_left (mul_lt_mul_of_pos_right hx' eadivpos))
        (mul_lt_mul_of_pos_left hy' ebdivpos).le
    _ ≤ e := PreReal.mul_rat_cond1 hepos he hapos hbpos

theorem neg_sub_neg (x y : Rat) : -x - -y ~= y - x := by
  cnsimp only [sub_eq_add_neg, neg_neg, add_comm y, eq'_self_iff]

theorem PreReal.mul_rat_cond'' {a b e x y x' y' : Rat}
    (he : 0 < e)
    (hx : x.abs < a) (hy : y.abs < b)
    (hx' : x'.abs < a) (hy' : y'.abs < b)
    (hxx' : (x - x').abs < (e.min (8 * a * b)) / b / 4)
    (hyy' : (y - y').abs < (e.min (8 * a * b)) / a / 4) :
    x * y - x' * y' < e := by
  refine lt_of_lt_of_le (y := e.min (8 * a * b)) ?_ (Rat.min_le_of_left_le (Rat.le_refl e))
  generalize he'_eq : e.min (8 * a * b) = e' at *
  have apos : 0 < a := lt_of_le_of_lt (Rat.abs_nonneg x) hx
  have bpos : 0 < b := lt_of_le_of_lt (Rat.abs_nonneg y) hy
  have he'pos : 0 < e' := by
    rw [← he'_eq]
    cnsimp [Rat.lt_min]
    constructor
    · exact he
    · exact mul_pos (mul_pos (by decide) apos) bpos
  have he' : e' ≤ 8 * a * b := he'_eq ▸ Rat.min_le_of_right_le (Rat.le_refl _)
  clear he'_eq he e
  cnsimp only [Rat.abs_lt, neg_sub] at hx hy hx' hy'
  by_cases' h : 0 ≤ x
  · by_cases' h' : 0 ≤ y
    · exact PreReal.mul_rat_cond' (.inl ⟨h, h'⟩) apos bpos hx'.1 hy'.1
        he' he'pos hxx' hyy'
    · replace h' := neg_nonneg.mpr (Rat.le_of_not_le h')
      have h1 : (x' - x).abs < e' / b / 4 := by
        cnsimp only [Rat.abs_sub_comm x', hxx']
      have h2 : (-y' - -y).abs < e' / a / 4 := by
        cnsimp only [neg_sub_neg, hyy']
      have := PreReal.mul_rat_cond' (.inr ⟨h, h'⟩) apos bpos hx.1 hy.2 he' he'pos h1 h2
      cnsimp only [mul_neg, neg_sub_neg] at this
      exact this
  · replace h := neg_nonneg.mpr (Rat.le_of_not_le h)
    by_cases' h' : 0 ≤ y
    · have h1 : (-x' - -x).abs < e' / b / 4 := by
        cnsimp only [neg_sub_neg x', hxx']
      have h2 : (y' - y).abs < e' / a / 4 := by
        cnsimp only [Rat.abs_sub_comm y', hyy']
      have := PreReal.mul_rat_cond' (.inr ⟨h, h'⟩) apos bpos hx.2 hy.1 he' he'pos h1 h2
      cnsimp only [mul_neg, neg_mul, neg_sub_neg] at this
      exact this
    · replace h' := neg_nonneg.mpr (Rat.le_of_not_le h')
      have h1 : (-x - -x').abs < e' / b / 4 := by
        cnsimp only [neg_sub_neg x, Rat.abs_sub_comm x', hxx']
      have h2 : (-y - -y').abs < e' / a / 4 := by
        cnsimp only [neg_sub_neg y, Rat.abs_sub_comm y', hyy']
      have := PreReal.mul_rat_cond' (x := -x) (y := -y) (.inl ⟨h, h'⟩) apos bpos hx'.2 hy'.2 he' he'pos h1 h2
      cnsimp only [neg_sub_neg, neg_mul, mul_neg] at this
      exact this

theorem PreReal.mul_rat_cond {a b e x y x' y' : Rat}
    (he : 0 < e)
    (hx : x.abs < a) (hy : y.abs < b)
    (hx' : x'.abs < a) (hy' : y'.abs < b)
    (hxx' : (x - x').abs < (e.min (8 * a * b)) / b / 4)
    (hyy' : (y - y').abs < (e.min (8 * a * b)) / a / 4) :
    (x * y - x' * y').abs < e := by
  cnsimp only [Rat.abs_lt, neg_sub]
  constructor
  · exact PreReal.mul_rat_cond'' he hx hy hx' hy' hxx' hyy'
  · cnsimp only [Rat.abs_sub_comm x, Rat.abs_sub_comm y] at hxx' hyy'
    exact PreReal.mul_rat_cond'' he hx' hy' hx hy hxx' hyy'

def PreReal.mul (x y : PreReal) : PreReal where
  seq i := (x.seq i).bind fun' a => (y.seq i).map (fun' b => a * b)
  isCauSeq ε hε := by
    refine x.exists_gt_abs_seq.elim fun a ha => ?_
    refine y.exists_gt_abs_seq.elim fun b hb => ?_
    have apos : 0 < a := by
      specialize ha 0
      refine (x.seq 0).elim fun c hc => ?_
      cnsimp [hc] at ha
      exact lt_of_le_of_lt (Rat.abs_nonneg c) ha
    have bpos : 0 < b := by
      specialize hb 0
      refine (y.seq 0).elim fun c hc => ?_
      cnsimp [hc] at hb
      exact lt_of_le_of_lt (Rat.abs_nonneg c) hb
    have minpos : 0 < ε.min (8 * a * b) :=
      Rat.lt_min.mpr ⟨hε, mul_pos (mul_pos (by decide) apos) bpos⟩
    refine (x.isCauSeq (ε.min (8 * a * b) / b / 8) ?_).elim fun i hi => ?_
    · exact div_pos (div_pos minpos bpos) (by decide)
    refine (y.isCauSeq (ε.min (8 * a * b) / a / 8) ?_).elim fun i' hi' => ?_
    · exact div_pos (div_pos minpos apos) (by decide)
    refine .intro (max i i') fun j hj => ?_
    replace hj := Nat.max_le'.mp hj
    have hi1 := hi (max i i') (Nat.le_max_left' ..)
    have hi2 := hi j hj.1
    have hi'1 := hi' (max i i') (Nat.le_max_right' ..)
    have hi'2 := hi' j hj.2
    have ha1 := ha (max i i')
    have hb1 := hb (max i i')
    have ha2 := ha j
    have hb2 := hb j
    refine (x.seq i).elim fun c hc => ?_
    refine (y.seq i').elim fun c' hc' => ?_
    refine (x.seq (max i i')).elim fun d hd => ?_
    refine (y.seq (max i i')).elim fun d' hd' => ?_
    refine (x.seq j).elim fun e he => ?_
    refine (y.seq j).elim fun e' he' => ?_
    cnsimp only [hc, hc', hd, hd', he, he', Noncomputable.test_mk,
      Noncomputable.bind_mk, Noncomputable.map_mk, Fun.apply_mkFun']
      at hi1 hi2 hi'1 hi'2 ha1 hb1 ha2 hb2 ⊢
    cnsimp only [Rat.abs_sub_comm d, Rat.abs_sub_comm d'] at hi1 hi'1
    replace hi := Rat.abs_sub_lt_trans hi1 hi2
    replace hi' := Rat.abs_sub_lt_trans hi'1 hi'2
    cnsimp only [(div_eq_mul_inv · (8 : Rat)), ← Rat.mul_add, show 8⁻¹ + 8⁻¹ ~= (4⁻¹ : Rat) from rfl] at hi hi'
    cnsimp only [← div_eq_mul_inv] at hi hi'
    exact PreReal.mul_rat_cond hε ha2 hb2 ha1 hb1 hi hi'

theorem PreReal.mul_of_eq'_zero (x y : PreReal) (hy : y ~= 0) : x.mul y ~= 0 := by
  cnsimp only [eqv_def, seq_ofNat, Noncomputable.test_mk, Fun.apply_mkFun',
    zero_sub, Rat.abs_neg] at hy ⊢
  dsimp only [mul]
  refine x.exists_gt_abs_seq.elim fun a ha => ?_
  have apos : 0 < a := by
      specialize ha 0
      refine (x.seq 0).elim fun c hc => ?_
      cnsimp [hc] at ha
      exact lt_of_le_of_lt (Rat.abs_nonneg c) ha
  intro ε hε
  specialize hy (ε / a) (div_pos hε apos)
  refine hy.elim fun i hi => ?_
  refine .intro i fun j hj => ?_
  specialize ha j
  specialize hi j hj
  refine (x.seq j).elim fun b hb => ?_
  refine (y.seq j).elim fun c hc => ?_
  cnsimp only [hb, hc, Noncomputable.test_mk, Noncomputable.bind_mk,
    Noncomputable.map_mk, Fun.apply_mkFun'] at ha hi ⊢
  cnsimp only [Rat.abs_mul]
  calc
    b.abs * c.abs < a * (ε / a) :=
      mul_lt_mul' ha.le hi (Rat.abs_nonneg _) apos
    _ ~= ε := mul_div_cancel apos.ne' _

protected theorem PreReal.mul_neg (x y : PreReal) : x.mul y.neg ~= (x.mul y).neg := by
  apply eqv_of_seq_eq
  intro i
  dsimp [PreReal.mul, PreReal.neg]
  refine (x.seq i).elim fun a ha => ?_
  refine (y.seq i).elim fun b hb => ?_
  cnsimp only [ha, hb, Noncomputable.bind_mk, Noncomputable.map_mk, seq_ofNat, Fun.apply_mkFun',
    Noncomputable.mk_inj, mul_neg, eq'_self_iff]

protected theorem PreReal.mul_zero (x : PreReal) : x.mul 0 ~= 0 := by
  apply eqv_of_seq_eq
  intro i
  dsimp [PreReal.mul]
  refine (x.seq i).elim fun a ha => ?_
  cnsimp only [ha, Noncomputable.bind_mk, Noncomputable.map_mk, seq_ofNat, Fun.apply_mkFun',
    Noncomputable.mk_inj]
  exact mul_zero a

protected theorem PreReal.mul_one (x : PreReal) : x.mul 1 ~= x := by
  apply eqv_of_seq_eq
  intro i
  dsimp [PreReal.mul]
  refine (x.seq i).elim fun a ha => ?_
  cnsimp only [ha, Noncomputable.bind_mk, Noncomputable.map_mk, seq_ofNat, Fun.apply_mkFun',
    Noncomputable.mk_inj]
  exact mul_one a

protected theorem PreReal.mul_comm (x y : PreReal) : x.mul y ~= y.mul x := by
  apply eqv_of_seq_eq
  intro i
  dsimp [PreReal.mul]
  refine (x.seq i).elim fun a ha => ?_
  refine (y.seq i).elim fun b hb => ?_
  cnsimp only [ha, hb, Noncomputable.bind_mk, Noncomputable.map_mk, Fun.apply_mkFun',
    mul_comm a, eq'_self_iff]

protected theorem PreReal.mul_assoc (x y z : PreReal) : (x.mul y).mul z ~= x.mul (y.mul z) := by
  apply eqv_of_seq_eq
  intro i
  dsimp [PreReal.mul]
  refine (x.seq i).elim fun a ha => ?_
  refine (y.seq i).elim fun b hb => ?_
  refine (z.seq i).elim fun c hc => ?_
  cnsimp only [ha, hb, hc, Noncomputable.bind_mk, Noncomputable.map_mk, Fun.apply_mkFun',
    mul_assoc, eq'_self_iff]

-- returns the index of the smallest index `≤ i` for which `p` holds or `none`.
def Nat.minRanged (p : Nat → Prop) (i : Nat) : Noncomputable (Option Nat) :=
  match i with
  | 0 => .ite (p i) (.mk (some i)) (.mk none)
  | k + 1 =>
    (minRanged p k).bind (Fun.mkFun' (fun a =>
    match a with
    | none => .ite (p i) (.mk (some i)) (.mk none)
    | some i => .mk (some i)) (fun h => by
      dsimp
      split <;> split <;> try contradiction
      · rfl
      · cnsimp only [h, eq'_self_iff]))

theorem Nat.well_founded_exists' {p : Nat → Prop}
    (h : ∀ i, p i → ∃' j, j < i ∧ p j) (i : Nat) : ¬p i := by
  intro h'
  induction i using Nat.strongRecOn with
  | ind k ih =>
    specialize h k h'
    refine h.elim fun a ha => ?_
    exact ih a ha.1 ha.2

theorem Nat.minRanged_eq_some_iff (p : Nat → Prop) [∀ x, DNE (p x)] (i k : Nat) :
    minRanged p i ~= .mk (some k) ↔ k ≤ i ∧ p k ∧ ∀ k' < k, ¬p k' := by
  induction i generalizing k with
  | zero =>
    dsimp [minRanged]
    by_cases' h : p 0
    · cnsimp only [h, Noncomputable.ite_true, Noncomputable.mk_inj, Option.some.inj'_iff]
      constructor
      · rintro rfl
        exact ⟨Nat.le_refl _, h, fun _ _ => by contradiction⟩
      · intro h'
        match k, h'.1 with
        | 0, _ => rfl
    · cnsimp only [h, Noncomputable.ite_false, Noncomputable.mk_inj, Option.none_eq'_some,
        false_iff_iff]
      intro h'
      match k, h'.1 with
      | 0, _ => exact (h h'.2.1).elim
  | succ n ih =>
    dsimp [minRanged]
    refine (minRanged p n).elim fun a ha => ?_
    cnsimp only [ha, Noncomputable.bind_mk, Fun.apply_mkFun'] at ih ⊢
    split
    · cnsimp only [Noncomputable.mk_inj, Option.none_eq'_some, false_iff_iff] at ih
      by_cases' h : p (n + 1)
      · cnsimp only [h, Noncomputable.ite_true, Noncomputable.mk_inj, Option.some.inj'_iff]
        constructor
        · rintro rfl
          repeat' constructor
          · exact h
          · cnsimp only [not_and, not_forall_iff_exists', not_implies, not_not] at ih
            intro k
            cnsimp only [← not_and]
            apply Nat.well_founded_exists' (p := fun k => k < n + 1 ∧ p k)
            intro i hi
            refine (ih i (Nat.le_of_lt_add_one hi.1) hi.2).elim fun a ha => ?_
            refine .intro a ⟨ha.1, trans ha.1 hi.1, ha.2⟩
        · intro h'
          refine h'.1.casesOn (fun h h' ih h'' => ?_) (fun hle h h' ih h'' => ?_) h h' ih (show n + 1 = n.succ from rfl)
          · rfl
          · cases Nat.succ.inj h''
            exact (ih k ⟨‹_›, h'.2⟩).elim
      · cnsimp only [h, Noncomputable.ite_false, Noncomputable.mk_inj, Option.none_eq'_some,
          false_iff_iff]
        intro h'
        refine h'.1.casesOn (fun h h' ih h'' => ?_) (fun hle h h' ih h'' => ?_) h h' ih (show n + 1 = n.succ from rfl)
        · exact h h'.2.1
        · cases Nat.succ.inj h''
          exact (ih k ⟨‹_›, h'.2⟩).elim
    · cnsimp only [Noncomputable.mk_inj, Option.some.inj'_iff] at ih ⊢
      constructor
      · intro h
        cnsimp only [ih] at h
        exact ⟨Nat.le_add_right_of_le h.1, h.2⟩
      · intro h
        refine h.1.casesOn (fun heq => ?_) (fun hle heq => ?_) (show n + 1 = n.succ from rfl)
        · cases heq
          replace ih := (ih _).mp .rfl
          exact (h.2.2 _ (Nat.lt_succ_of_le ih.1) ih.2.1).elim
        · cases Nat.succ.inj heq
          cnsimp only [ih]
          exact ⟨hle, h.2⟩

theorem Nat.minRanged_eq_none_iff (p : Nat → Prop) [∀ x, DNE (p x)] (i : Nat) :
    minRanged p i ~= .mk none ↔ ∀ k ≤ i, ¬p k := by
  refine (minRanged p i).elim fun a ha => ?_
  have := Nat.minRanged_eq_some_iff p i
  cnsimp only [ha, Noncomputable.mk_inj] at this
  match a with
  | none =>
    cnsimp only [Option.none_eq'_some, false_iff_iff, not_and, not_forall_iff_exists',
      not_implies, not_not] at this
    cnsimp only [ha, eq'_self_iff, true_iff_iff]
    intro k'
    cnsimp only [← not_and]
    apply Nat.well_founded_exists' (p := fun k => k ≤ i ∧ p k)
    intro k' hk'
    refine (this k' hk'.1 hk'.2).elim fun a ha => ?_
    exact .intro a ⟨ha.1, Nat.le_trans (Nat.le_of_lt ha.1) hk'.1, ha.2⟩
  | some k =>
    cnsimp only [Option.some.inj'_iff] at this
    cnsimp only [ha, Noncomputable.mk_inj, Option.some_eq'_none, false_iff_iff]
    intro h
    replace this := (this k).mp .rfl
    exact h k this.1 this.2.1

theorem Option.isSome_iff_ne'_none [Eqv α] {x : Option α} : x.isSome ↔ x ~!= none := by
  cases x
  · constructor
    · intro
      contradiction
    · intro h
      exact (h .rfl).elim
  · constructor
    · intro _ _
      contradiction
    · intro _
      rfl

-- returns the first occurrence
def Nat.choose_of_exists {p : Nat → Prop} [∀ x, DNE (p x)] (h : ∃' x, p x) : Noncomputable Nat := by
  apply Noncomputable.uniqueChoice (fun' a => p a ∧ ∀ i < a, ¬p i)
  cnsimp only [Fun.apply_mkFun']
  refine h.elim fun a ha => ?_
  refine (Nat.minRanged p a).elim fun b hb => ?_
  have : b.isSome := by
    apply Option.isSome_iff_ne'_none.mpr
    have := Nat.minRanged_eq_none_iff p a
    cnsimp only [hb, Noncomputable.mk_inj] at this
    cnsimp only [ne'_iff, this]
    intro h'
    exact h' a (Nat.le_refl _) ha
  match b, this with
  | some c, _ =>
  refine .intro c ?_
  constructor
  · exact ((Nat.minRanged_eq_some_iff p a c).mp hb).2
  · intro y hy
    have := (Nat.minRanged_eq_some_iff p a y).mpr ?_
    · cnsimp [hb] at this
      exact this
    · constructor
      · apply DNE.dne fun h => ?_
        cnsimp only [Nat.not_le] at h
        exact hy.2 a h ha
      · exact hy

theorem PreReal.pos_trichotomy (x : PreReal) : x ~= 0 ∨' x.pos ∨' x.neg.pos := by
  dsimp only [pos, neg]
  cnsimp only [eqv_def]
  apply or'_iff_not_imp.mpr
  cnsimp only [not_forall_iff_exists', not_implies, not_exists', seq_ofNat,
    Noncomputable.test_mk, Fun.apply_mkFun', zero_sub, Rat.abs_neg]
  intro h
  refine h.elim fun ε hε => ?_
  clear h
  obtain ⟨hε, h⟩ := hε
  apply or'_iff_not_imp.mpr
  cnsimp only [not_forall_iff_exists', not_implies, not_exists', not_and]
  intro h'
  intro h''
  dsimp at h''
  cnsimp only [not_forall_iff_exists', not_implies, not_exists', not_and] at h''
  specialize h' (ε / 2) (div_pos hε (by decide))
  specialize h'' (ε / 2) (div_pos hε (by decide))
  refine (x.isCauSeq (ε / 4) (div_pos hε (by decide))).elim fun i hi => ?_
  specialize h i
  specialize h' i
  specialize h'' i
  refine h.elim fun j hj => ?_
  refine h'.elim fun j' hj' => ?_
  refine h''.elim fun j'' hj'' => ?_
  clear h h' h''
  have hi1 := hi j hj.1
  have hi2 := hi j' hj'.1
  have hi3 := hi j'' hj''.1
  refine (x.seq i).elim fun a ha => ?_
  refine (x.seq j).elim fun b hb => ?_
  refine (x.seq j').elim fun b' hb' => ?_
  refine (x.seq j'').elim fun b'' hb'' => ?_
  cnsimp only [ha, hb, hb', hb'', Noncomputable.test_mk, Noncomputable.map_mk,
    Fun.apply_mkFun'] at hi1 hi2 hi3 hj hj' hj''
  replace hj := hj.2
  replace hj' := hj'.2
  replace hj'' := hj''.2
  dsimp at *
  cnsimp only [not_lt] at hj hj' hj''
  cnsimp only [Rat.abs_sub_comm b] at hi1
  have h := Rat.abs_sub_lt_trans hi1 hi2
  have h' := Rat.abs_sub_lt_trans hi1 hi3
  have : ε / 4 + ε / 4 ~= ε / 2 := by
    cnsimp only [div_eq_mul_inv, ← Rat.mul_add, show 4⁻¹ + 4⁻¹ ~= (2⁻¹ : Rat) from rfl]
    rfl
  cnsimp only [Rat.abs_lt, neg_sub, this] at h h'
  cnsimp only [Rat.le_abs] at hj
  refine hj.elim (fun hj => ?_) (fun hj => ?_)
  · cnsimp only [sub_lt_iff_lt_add] at h h'
    apply lt_irrefl ε
    calc
      ε ≤ b := hj
      _ < ε / 2 + b' := h.2
      _ ≤ ε / 2 + ε / 2 := add_le_add_left hj'
      _ ~= ε := Rat.half_add_half ε
  · cnsimp only [sub_eq_add_neg, add_comm b''] at h'
    cnsimp only [← lt_sub_iff_add_lt, sub_eq_add_neg] at h'
    apply lt_irrefl ε
    calc
      ε ≤ -b := hj
      _ < ε / 2 + -b'' := h'.1
      _ ≤ ε / 2 + ε / 2 := add_le_add_left hj''
      _ ~= ε := Rat.half_add_half ε

protected theorem PreReal.not_zero_pos : ¬(0 : PreReal).pos := by
  intro h
  dsimp only [pos] at h
  refine h.elim fun ε hε => ?_
  refine hε.2.elim fun i hi => ?_
  specialize hi i (Nat.le_refl _)
  cnsimp only [PreReal.seq_ofNat, Noncomputable.test_mk, Fun.apply_mkFun'] at hi
  exact lt_asymm hε.1 hi

protected theorem PreReal.one_pos : (1 : PreReal).pos := by
  dsimp only [pos]
  refine .intro (1 / 2) ⟨by decide, ?_⟩
  refine .intro 0 fun j hj => ?_
  cnsimp; decide

protected theorem PreReal.add_pos {x y : PreReal} (hx : x.pos) (hy : y.pos) : (x.add y).pos := by
  dsimp [pos, PreReal.add] at hx hy ⊢
  refine hx.elim fun ε hε => ?_
  refine hy.elim fun ε' hε' => ?_
  refine .intro (ε + ε') ⟨add_pos hε.1 hε'.1.le, ?_⟩
  refine hε.2.elim fun i hi => ?_
  refine hε'.2.elim fun i' hi' => ?_
  refine .intro (max i i') fun j hj => ?_
  replace hj := Nat.max_le'.mp hj
  specialize hi j hj.1
  specialize hi' j hj.2
  refine (x.seq j).elim fun a ha => ?_
  refine (y.seq j).elim fun b hb => ?_
  cnsimp only [ha, hb, Noncomputable.bind_mk, Fun.apply_mkFun',
    Noncomputable.test_mk] at hi hi' ⊢
  exact add_lt_add hi hi'.le

protected theorem PreReal.mul_pos {x y : PreReal} (hx : x.pos) (hy : y.pos) : (x.mul y).pos := by
  dsimp [pos, PreReal.mul] at hx hy ⊢
  refine hx.elim fun ε hε => ?_
  refine hy.elim fun ε' hε' => ?_
  refine .intro (ε * ε') ⟨mul_pos hε.1 hε'.1, ?_⟩
  refine hε.2.elim fun i hi => ?_
  refine hε'.2.elim fun i' hi' => ?_
  refine .intro (max i i') fun j hj => ?_
  replace hj := Nat.max_le'.mp hj
  specialize hi j hj.1
  specialize hi' j hj.2
  refine (x.seq j).elim fun a ha => ?_
  refine (y.seq j).elim fun b hb => ?_
  cnsimp only [ha, hb, Noncomputable.bind_mk, Noncomputable.map_mk,
    Fun.apply_mkFun', Noncomputable.test_mk] at hi hi' ⊢
  exact mul_lt_mul hi hi'.le hε'.1 (hε.1.le.trans hi.le)

protected theorem PreReal.mul_add (x y z : PreReal) : x.mul (y.add z) ~= (x.mul y).add (x.mul z) := by
  apply eqv_of_seq_eq
  intro i
  dsimp only [mul, PreReal.add]
  refine (x.seq i).elim fun a ha => ?_
  refine (y.seq i).elim fun b hb => ?_
  refine (z.seq i).elim fun c hc => ?_
  cnsimp [ha, hb, hc, mul_add]

theorem PreReal.eq'_of_sub_eq'_zero {x y : PreReal} (h : x.add y.neg ~= 0) : x ~= y := by
  calc
    x ~= (x.add y.neg).add y := by
      cnsimp only [PreReal.add_assoc, PreReal.add_comm y.neg,
        PreReal.add_neg, PreReal.add_zero, eq'_self_iff]
    _ ~= y := by cnsimp only [h, PreReal.add_comm 0, PreReal.add_zero, eq'_self_iff]

@[ccongr]
protected theorem PreReal.mul_congr {x₁ x₂ y₁ y₂ : PreReal} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁.mul y₁ ~= x₂.mul y₂ := by
  have xdiff : x₁.add x₂.neg ~= 0 := by
    cnsimp only [hx, PreReal.add_neg, eq'_self_iff]
  have ydiff : y₁.add y₂.neg ~= 0 := by
    cnsimp only [hy, PreReal.add_neg, eq'_self_iff]
  have h' := PreReal.mul_of_eq'_zero x₁ _ ydiff
  cnsimp only [PreReal.mul_add, PreReal.mul_neg] at h'
  replace h' := PreReal.eq'_of_sub_eq'_zero h'
  refine h'.trans ?_
  cnsimp only [(PreReal.mul_comm · y₂)]
  have h'' := PreReal.mul_of_eq'_zero y₂ _ xdiff
  cnsimp only [PreReal.mul_add, PreReal.mul_neg] at h''
  exact PreReal.eq'_of_sub_eq'_zero h''

theorem PreReal.neg_add_cancel (x : PreReal) : x.neg.add x ~= 0 := by
  cnsimp only [PreReal.add_comm x.neg, PreReal.add_neg, eq'_self_iff]

theorem PreReal.neg_add (x y : PreReal) : (x.add y).neg ~= y.neg.add x.neg := by
  calc
    (x.add y).neg ~= (x.add y).neg.add ((x.add (y.add y.neg)).add x.neg) := by
      cnsimp only [PreReal.add_neg, PreReal.add_zero, eq'_self_iff]
    _ ~= ((x.add y).neg.add (x.add y)).add (y.neg.add x.neg) := by
      cnsimp only [PreReal.add_assoc, eq'_self_iff]
    _ ~= y.neg.add x.neg := by
      cnsimp only [PreReal.add_comm (x.add y).neg, PreReal.add_neg,
        PreReal.add_comm 0, PreReal.add_zero, eq'_self_iff]

theorem PreReal.neg_neg (x : PreReal) : x.neg.neg ~= x := by
  calc
    x.neg.neg ~= x.neg.neg.add (x.neg.add x) := by
      cnsimp only [PreReal.add_comm x.neg, PreReal.add_neg, PreReal.add_zero, eq'_self_iff]
    _ ~= x := by
      cnsimp only [← PreReal.add_assoc, PreReal.add_comm x.neg.neg x.neg, PreReal.add_neg,
        PreReal.add_comm 0, PreReal.add_zero, eq'_self_iff]
