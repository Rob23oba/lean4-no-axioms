import NoAxioms.Prelude

inductive ZFSet where
  | mk' (α : Type u) (f : α → ZFSet)

def ZFSet.Equiv : ZFSet → ZFSet → Prop'
  | ⟨_, f⟩, ⟨_, g⟩ =>
    (∀ x, ∃' y, (f x).Equiv (g y))
    ∧ (∀ x, ∃' y, (f y).Equiv (g x))

theorem ZFSet.Equiv.rfl {a : ZFSet} : a.Equiv a := by
  induction a with
  | mk' α f ih =>
  dsimp [ZFSet.Equiv]
  constructor
  · intro x
    refine .intro x ?_
    exact ih x
  · intro x
    refine .intro x ?_
    exact ih x

theorem ZFSet.Equiv.comm {a b : ZFSet} : a.Equiv b ↔ b.Equiv a := by
  induction a generalizing b with
  | mk' α f ih =>
  rcases b with ⟨β, g⟩
  dsimp [ZFSet.Equiv]
  cnsimp [ih]
  exact and_comm

theorem ZFSet.Equiv.trans {a b c : ZFSet} (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c := by
  induction b generalizing a c with
  | mk' α f ih =>
  rcases a with ⟨β, g⟩
  rcases c with ⟨β', g'⟩
  dsimp [ZFSet.Equiv] at h h' ⊢
  constructor
  · intro x
    replace h := h.1 x
    refine h.elim (fun y hy => ?_)
    replace h' := h'.1 y
    refine h'.elim (fun z hz => ?_)
    exact .intro z (ih y hy hz)
  · intro x
    replace h' := h'.2 x
    refine h'.elim (fun y hy => ?_)
    replace h := h.2 y
    refine h.elim (fun z hz => ?_)
    exact .intro z (ih y hz hy)

instance : Eqv ZFSet where
  eqv := ZFSet.Equiv
  refl _ := ZFSet.Equiv.rfl
  symm h := ZFSet.Equiv.comm.mp h
  trans h h' := ZFSet.Equiv.trans h h'

@[ccongr]
theorem ZFSet.Equiv.congr {a₁ a₂ b₁ b₂ : ZFSet.{u}} (ha : a₁ ~= a₂) (hb : b₁ ~= b₂) :
    a₁.Equiv b₁ ↔ a₂.Equiv b₂ :=
  eq'_congr ha hb

def ZFSet.mk (α : Type u) [Eqv α] (f : α ~> ZFSet) : ZFSet :=
  ⟨α, f⟩

theorem ZFSet.mk_eq'_mk_iff {α : Type u} {β : Type u} [Eqv α] [Eqv β]
    {f : α ~> ZFSet} {g : β ~> ZFSet} :
    mk α f ~= mk β g ↔ (∀ x, ∃' y, f x ~= g y) ∧ (∀ x, ∃' y, f y ~= g x) := Iff.rfl

@[cnsimp]
theorem ZFSet.mk'_eq'_mk'_iff {α : Type u} {β : Type u} {f : α → ZFSet} {g : β → ZFSet} :
    mk' α f ~= mk' β g ↔ (∀ x, ∃' y, f x ~= g y) ∧ (∀ x, ∃' y, f y ~= g x) := Iff.rfl

@[ccongr]
theorem ZFSet.mk_congr {α : Type u} [Eqv α] {f₁ f₂ : α ~> ZFSet}
    (hf : f₁ ~= f₂) : mk α f₁ ~= mk α f₂ := by
  cnsimp only [ZFSet.mk_eq'_mk_iff]
  cnsimp [hf]
  exact ZFSet.Equiv.rfl (a := mk α f₂)

def ZFSet.Mem (a b : ZFSet) : Prop' :=
  match b with
  | ⟨_, f⟩ => ∃' x, a ~= f x

def ZFSet.Subset (a b : ZFSet) : Prop' :=
  match a, b with
  | ⟨_, f⟩, ⟨_, g⟩ => ∀ x, ∃' y, f x ~= g y

instance : Membership ZFSet ZFSet where
  mem a b := ZFSet.Mem b a

instance : HasSubset ZFSet where
  Subset a b := ZFSet.Subset a b

instance {x y : ZFSet} : DNE (x ∈ y) := inferInstanceAs (DNE (Prop'.p _))
instance {x y : ZFSet} : DNE (x ⊆ y) := inferInstanceAs (DNE (Prop'.p _))

@[cnsimp]
theorem ZFSet.mem_mk' (x : ZFSet) (α : Type u) (f : α → ZFSet) :
    x ∈ mk' α f ↔ ∃' a, x ~= f a := Iff.rfl

@[cnsimp]
theorem ZFSet.mk'_subset_mk' (α : Type u) (f : α → ZFSet) (β : Type u) (g : β → ZFSet) :
    mk' α f ⊆ mk' β g ↔ ∀ a, ∃' b, f a ~= g b := Iff.rfl

@[ccongr]
theorem ZFSet.mem_congr {x₁ x₂ y₁ y₂ : ZFSet} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ ∈ y₁ ↔ x₂ ∈ y₂ := by
  rcases y₁ with ⟨β₁, g₁⟩
  rcases y₂ with ⟨β₂, g₂⟩
  cnsimp only [mem_mk']
  cnsimp only [mk'_eq'_mk'_iff] at hy
  constructor
  · intro h
    refine h.elim (fun a ha => ?_)
    replace hy := hy.1 a
    refine hy.elim (fun b hb => ?_)
    exact .intro b ((hx.symm.trans ha).trans hb)
  · intro h
    refine h.elim (fun a ha => ?_)
    replace hy := hy.2 a
    refine hy.elim (fun b hb => ?_)
    exact .intro b ((hx.trans ha).trans hb.symm)

theorem ZFSet.subset_iff {x y : ZFSet} : x ⊆ y ↔ ∀ a ∈ x, a ∈ y := by
  rcases x with ⟨α, f⟩
  rcases y with ⟨β, g⟩
  cnsimp only [mk'_subset_mk', mem_mk']
  constructor
  · intro h a ha
    refine ha.elim (fun b hb => ?_)
    cnsimp [hb]
    exact h b
  · intro h a
    exact h (f a) (.intro a .rfl)

@[ccongr]
theorem ZFSet.subset_congr {x₁ x₂ y₁ y₂ : ZFSet} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) :
    x₁ ⊆ y₁ ↔ x₂ ⊆ y₂ := by
  cnsimp [subset_iff, hx, hy]

def ZFSet.empty := mk PEmpty (fun' a => a.elim)
def ZFSet.singleton (x : ZFSet) := mk PUnit (fun' a => x)

instance : EmptyCollection ZFSet := ⟨ZFSet.empty⟩
instance : Singleton ZFSet ZFSet := ⟨ZFSet.singleton⟩

@[ccongr]
theorem ZFSet.singleton_congr {x₁ x₂ : ZFSet} (hx : x₁ ~= x₂) :
    {x₁} ~= ({x₂} : ZFSet) := by
  dsimp [{·}, singleton]
  cnsimp only [mk_eq'_mk_iff, Fun.apply_mkFun']
  constructor
  · intro _; exact .intro ⟨⟩ hx
  · intro _; exact .intro ⟨⟩ hx

@[cnsimp]
theorem ZFSet.mem_empty (x : ZFSet) : x ∈ (∅ : ZFSet) ↔ False := by
  dsimp [EmptyCollection.emptyCollection, empty, · ∈ ·, Mem, mk]
  constructor
  · intro h
    exact h.elim fun a ha => a.elim
  · intro h
    exact h.elim

@[cnsimp]
theorem ZFSet.mem_singleton (x y : ZFSet) : x ∈ ({y} : ZFSet) ↔ x ~= y := by
  dsimp [{·}, singleton, · ∈ ·, Mem, mk]
  cnsimp
  constructor
  · intro h
    exact h.elim fun a ha => ha
  · intro h
    exact .intro ⟨⟩ h

theorem ZFSet.ext {x y : ZFSet} (h : ∀ a, a ∈ x ↔ a ∈ y) : x ~= y := by
  rcases x with ⟨α, f⟩
  rcases y with ⟨β, g⟩
  dsimp [· ∈ ·, Mem] at h
  cnsimp [mk'_eq'_mk'_iff]
  constructor
  · intro x
    exact (h (f x)).mp (.intro x .rfl)
  · intro x
    replace h := (h (g x)).mpr (.intro x .rfl)
    refine h.elim (fun a ha => ?_)
    exact .intro a ha.symm

theorem ZFSet.ext_iff {x y : ZFSet} : x ~= y ↔ ∀ a, a ∈ x ↔ a ∈ y := by
  constructor
  · intro h
    cnsimp [h]
    intro h'
    exact trivial
  · exact ZFSet.ext

def ZFSet.union (x y : ZFSet) :=
  match x, y with
  | ⟨α, f⟩, ⟨β, g⟩ =>
    mk' (α ⊕ β) (fun | .inl a => f a | .inr a => g a)

instance : Union ZFSet.{u} := ⟨ZFSet.union.{u, u}⟩

@[cnsimp]
theorem ZFSet.mem_union (x y z : ZFSet) : x ∈ y ∪ z ↔ x ∈ y ∨' x ∈ z := by
  rcases y with ⟨α, f⟩
  rcases z with ⟨β, g⟩
  dsimp [· ∪ ·, union, · ∈ ·, Mem]
  constructor
  · intro h
    refine h.elim (fun a ha => ?_)
    cases a
    · exact .inl (.intro _ ha)
    · exact .inr (.intro _ ha)
  · intro h
    refine h.elim (fun h' => h'.elim (fun a ha => ?_)) (fun h' => h'.elim (fun a ha => ?_))
    · exact .intro (.inl a) ha
    · exact .intro (.inr a) ha

@[ccongr]
theorem ZFSet.union_congr {x₁ x₂ y₁ y₂ : ZFSet} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ∪ y₁ ~= x₂ ∪ y₂ := by
  apply ZFSet.ext
  intro a
  cnsimp [hx, hy]

def ZFSet.filter (x : ZFSet) (p : ZFSet ~> Prop') :=
  match x with
  | ⟨_, f⟩ =>
    mk' {x // p (f x)} (fun ⟨a, _⟩ => f a)

@[cnsimp]
theorem ZFSet.mem_filter (x y : ZFSet) (p : ZFSet ~> Prop') : x ∈ y.filter p ↔ x ∈ y ∧ p x := by
  rcases y with ⟨α, f⟩
  dsimp [filter, · ∈ ·, Mem]
  constructor
  · intro h
    refine h.elim (fun a ha => ?_)
    have := a.2
    cnsimp only [← ha] at this
    exact ⟨.intro a ha, this⟩
  · intro ⟨h, h'⟩
    refine h.elim (fun a ha => ?_)
    cnsimp only [ha] at h'
    exact .intro ⟨a, h'⟩ ha

def ZFSet.inter (x y : ZFSet) :=
  x.filter (fun' a => a ∈ y)

instance : Inter ZFSet.{u} := ⟨ZFSet.inter⟩

@[cnsimp]
theorem ZFSet.mem_inter (x y z : ZFSet) : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
  dsimp [· ∩ ·, inter]
  cnsimp

@[ccongr]
theorem ZFSet.inter_congr {x₁ x₂ y₁ y₂ : ZFSet} (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁ ∩ y₁ ~= x₂ ∩ y₂ := by
  apply ZFSet.ext
  intro a
  cnsimp [hx, hy]

def ZFSet.image (x : ZFSet) (f : ZFSet ~> ZFSet) : ZFSet :=
  match x with
  | ⟨α, g⟩ => ⟨α, fun a => f (g a)⟩

@[cnsimp]
theorem ZFSet.mem_image (x y : ZFSet) (f : ZFSet ~> ZFSet) : x ∈ y.image f ↔ ∃' z, z ∈ y ∧ x ~= f z := by
  rcases y with ⟨α, g⟩
  dsimp [image, · ∈ ·, Mem]
  constructor
  · intro h
    refine h.elim (fun a ha => ?_)
    refine .intro (g a) ?_
    exact ⟨.intro a .rfl, ha⟩
  · intro h
    refine h.elim (fun a ⟨ha, ha'⟩ => ha.elim (fun b hb => ?_))
    refine .intro b ?_
    cnsimp [ha', hb]

@[ccongr]
theorem ZFSet.image_congr {x₁ x₂ : ZFSet} {f₁ f₂ : ZFSet ~> ZFSet} (hx : x₁ ~= x₂) (hf : f₁ ~= f₂) :
    x₁.image f₁ ~= x₂.image f₂ := by
  apply ext
  intro a
  cnsimp [hx, hf]

def ZFSet.type : ZFSet → Type u
  | ⟨α, _⟩ => α

def ZFSet.fun : (x : ZFSet) → (x.type → ZFSet)
  | ⟨_, f⟩ => f

def ZFSet.sUnion (x : ZFSet) : ZFSet :=
  match x with
  | ⟨α, f⟩ =>
    ⟨(x : α) × (f x).type,
      fun ⟨x, y⟩ => (f x).fun y⟩

@[cnsimp]
theorem ZFSet.mem_sUnion (x y : ZFSet) : x ∈ y.sUnion ↔ ∃' z, z ∈ y ∧ x ∈ z := by
  rcases y with ⟨α, f⟩
  dsimp [sUnion, · ∈ ·, Mem]
  constructor
  · intro h
    refine h.elim (fun ⟨a, b⟩ ha => ?_)
    dsimp at ha
    refine .intro (f a) ⟨.intro _ .rfl, ?_⟩
    generalize f a = z at *
    rcases z with ⟨β, g⟩
    exact .intro _ ha
  · intro h
    refine h.elim (fun a ⟨ha, ha'⟩ => ha.elim (fun b hb => ?_))
    rcases a with ⟨β, g⟩
    refine ha'.elim (fun c hc => ?_)
    suffices ∃' q, x ~= (f b).fun q by
      generalize hz : f b = z at hb this
      refine this.elim (fun q hq => ?_)
      refine .intro ⟨b, hz ▸ q⟩ ?_
      cases hz
      exact hq
    generalize f b = z at hb
    rcases z with ⟨β', g'⟩
    dsimp only [ZFSet.fun]
    cnsimp only [mk'_eq'_mk'_iff] at hb
    replace hb := hb.1 c
    refine hb.elim (fun d hd => ?_)
    refine .intro d ?_
    cnsimp [hc, hd]

@[ccongr]
theorem ZFSet.sUnion_congr {x₁ x₂ : ZFSet} (hx : x₁ ~= x₂) : x₁.sUnion ~= x₂.sUnion := by
  apply ext
  intro a
  cnsimp [hx]

def ZFSet.powerset (x : ZFSet) : ZFSet :=
  match x with
  | ⟨α, f⟩ =>
    ⟨α → Prop', fun p => ⟨{ x // p x }, fun x => f x⟩⟩

@[cnsimp]
theorem ZFSet.mem_powerset (x y : ZFSet) : x ∈ y.powerset ↔ x ⊆ y := by
  rcases x with ⟨α, f⟩
  rcases y with ⟨β, g⟩
  dsimp [powerset, · ∈ ·, Mem, · ⊆ ·, Subset]
  cnsimp only [mk'_eq'_mk'_iff]
  constructor
  · intro h
    refine h.elim (fun a ⟨ha, ha'⟩ => ?_)
    intro b
    replace ha := ha b
    refine ha.elim (fun c hc => ?_)
    exact .intro c.val hc
  · intro h
    refine .intro (fun y => ∃' x, f x ~= g y) ?_
    dsimp
    constructor
    · intro a
      refine (h a).elim (fun b hb => ?_)
      exact .intro ⟨b, .intro _ hb⟩ hb
    · intro ⟨a, ha⟩
      exact ha

@[ccongr]
theorem ZFSet.powerset_congr {x₁ x₂ : ZFSet} (hx : x₁ ~= x₂) : x₁.powerset ~= x₂.powerset := by
  apply ext
  intro a
  cnsimp [hx]

attribute [cnsimp] not_and

@[cnsimp]
theorem not_imp' [DNE p] [DNE q] : ¬(p → q) ↔ p ∧ ¬q := by
  constructor
  · intro h
    apply DNE.dne
    intro h'
    apply h
    intro hp
    apply DNE.dne
    intro hq
    exact h' ⟨hp, hq⟩
  · exact not_imp_of_and_not

@[cnsimp]
theorem not_forall {α : Type u} {p : α → Prop} [∀ x, DNE (p x)] : (¬∀ x, p x) ↔ ∃' x, ¬p x := by
  unfold Exists'
  cnsimp

@[cnsimp]
theorem not_exists' {α : Type u} {p : α → Prop} : (¬∃' x, p x) ↔ ∀ x, ¬p x := by
  unfold Exists'
  cnsimp only [not_not, iff_self_iff_true]

@[cnsimp]
theorem implies_true_iff (α : Sort u) : (α → True) ↔ True :=
  iff_true_intro (fun _ => trivial)

@[cnsimp]
theorem forall_exists'_index {α : Sort u} {p : α → Prop} {q : (∃' a, p a) → Prop}
    [∀ h, DNE (q h)] : (∀ h : (∃' x, p x), q h) ↔ ∀ x (h : p x), q (.intro x h) := by
  constructor
  · intro h x hx
    exact h (.intro x hx)
  · intro h h'
    exact h'.elim h

theorem DNE.by_contra [DNE p] (h : ¬p → False) : p := DNE.dne h

theorem ZFSet.ind (motive : ZFSet ~> Prop')
    (intro : (x : ZFSet) → (∀ y, y ∈ x → motive y) → motive x)
    (t : ZFSet) : motive t := by
  induction t with
  | mk' α f ih =>
    apply intro
    cnsimp only [mem_mk', forall_exists'_index]
    intro x y hy
    cnsimp [hy]
    apply ih

theorem ZFSet.axiom_of_extensionality : ∀ x y : ZFSet, (∀ z, z ∈ x ↔ z ∈ y) → x ~= y := by
  exact @ext

theorem ZFSet.axiom_of_regularity : ∀ x : ZFSet, (∃' a, a ∈ x) → ∃' y, y ∈ x ∧ ¬∃' z, z ∈ y ∧ z ∈ x := by
  intro x hx
  refine hx.elim (fun a ha => ?_)
  clear hx
  intro h'
  dsimp at h'
  cnsimp at h'
  revert ha h'
  apply a.ind (fun' a => a ∈ x → (∀ (b : ZFSet), b ∈ x → ∃' c, c ∈ b ∧ c ∈ x) → False) ?_
  dsimp [Fun.mkFun']
  intro a ih h h'
  refine (h' a h).elim (fun b hb => ?_)
  apply ih b hb.1 hb.2 h'

theorem ZFSet.axiom_of_specification (φ : ZFSet ~> Prop') : ∀ z : ZFSet, ∃' y : ZFSet, ∀ x, x ∈ y ↔ x ∈ z ∧ φ x := by
  intro z
  refine .intro (z.filter φ) ?_
  cnsimp

theorem ZFSet.axiom_of_pairing : ∀ x y : ZFSet, ∃' z : ZFSet, x ∈ z ∧ y ∈ z := by
  intro x y
  refine .intro ({x} ∪ {y}) ?_
  cnsimp

theorem ZFSet.axiom_of_union : ∀ F : ZFSet, ∃ A : ZFSet, ∀ Y x, (x ∈ Y ∧ Y ∈ F) → x ∈ A := by
  intro F
  refine .intro F.sUnion ?_
  intro Y x ⟨hx, hY⟩
  cnsimp only [mem_sUnion]
  exact .intro Y ⟨hY, hx⟩

theorem ZFSet.axiom_of_replacement (φ : ZFSet ~> ZFSet ~> Prop') :
    ∀ A : ZFSet, (∀ x, x ∈ A → ∃' y, φ x y ∧ ∀ y', φ x y' → y ~= y') → ∃' B : ZFSet, ∀ x, x ∈ A → ∃' y, y ∈ B ∧ φ x y := by
  intro A hA
