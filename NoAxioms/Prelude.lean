import NoAxioms.Tactic.TacticTesting
import NoAxioms.Tactic.CCongrTactic

elab "count_heartbeats" x:tactic : tactic => do
  let heartbeats ← IO.getNumHeartbeats
  Lean.Elab.Tactic.evalTactic x
  let heartbeatsNow ← IO.getNumHeartbeats
  Lean.logInfo m!"heartbeats: {heartbeatsNow - heartbeats}"

--set_option trace.compiler.ir.result true

class DNE (x : Prop) where
  dne : ¬¬x → x

instance [Decidable p] : DNE p := ⟨Decidable.not_not.mp⟩

instance {α : Sort u} {β : α → Prop} [∀ x, DNE (β x)] : DNE (∀ x, β x) where
  dne := fun h hp => DNE.dne fun hq => h fun h' => hq (h' hp)

instance {p q : Prop} [DNE p] [DNE q] : DNE (p ∧ q) where
  dne h :=
    ⟨DNE.dne fun h' => h fun h'' => h' h''.1,
     DNE.dne fun h' => h fun h'' => h' h''.2⟩

instance : DNE (¬p) :=
  inferInstanceAs (DNE (p → False))

instance {p q : Prop} [DNE p] [DNE q] : DNE (p ↔ q) where
  dne h :=
    ⟨DNE.dne fun h' => h fun h'' => h' h''.1,
     DNE.dne fun h' => h fun h'' => h' h''.2⟩

def Or' (p q : Prop) := ¬(¬p ∧ ¬q)
def Exists' {α : Sort u} (β : α → Prop) := ¬∀ x, ¬β x

infixr:30 " ∨' "  => Or'
macro "∃'" xs:Lean.explicitBinders ", " b:term : term => return ⟨← Lean.expandExplicitBinders ``Exists' xs b⟩

@[app_unexpander Exists'] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃' $xs:binderIdent*, $b) => `(∃' $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∃' $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃' ($x:ident : $t), $b)
  | _                                              => throw ()

instance : DNE (p ∨' q) :=
  inferInstanceAs (DNE (¬_))

instance {β : α → Prop} : DNE (∃' x, β x) :=
  inferInstanceAs (DNE (¬_))

theorem Or'.em (p : Prop) : p ∨' ¬p := by
  intro h
  exact h.2 h.1

theorem Or'.inl (h : p) : p ∨' q := by
  intro h'
  exact h'.1 h

theorem Or'.inr (h : q) : p ∨' q := by
  intro h'
  exact h'.2 h

theorem Or'.elim [DNE q] (h : p₁ ∨' p₂) (h₁ : p₁ → q) (h₂ : p₂ → q) : q := by
  apply DNE.dne
  intro h'
  apply h
  constructor
  · intro h''
    exact h' (h₁ h'')
  · intro h''
    exact h' (h₂ h'')

@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem Or'.rec {p q : Prop} {motive : p ∨' q → Prop} [∀ h, DNE (motive h)]
    (inl : (h : p) → motive (.inl h)) (inr : (h : q) → motive (.inr h)) (h : p ∨' q) : motive h :=
  Or'.elim h inl inr

theorem Exists'.intro (x : α) (h : p x) : Exists' p := by
  intro h'
  exact h' x h

theorem Exists'.elim {α : Sort u} {β : α → Prop} [DNE q] (h : ∃' x, β x) (h' : ∀ x, β x → q) : q := by
  apply DNE.dne
  intro h''
  apply h
  intro x
  intro h'''
  exact h'' (h' x h''')

@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem Exists'.rec {α : Sort u} {β : α → Prop} {motive : Exists' β → Prop} [∀ h, DNE (motive h)]
    (intro : (x : α) → (h : β x) → motive (.intro x h)) (h : Exists' β) : motive h :=
  Exists'.elim h intro

theorem DNE.byCases {p q : Prop} [DNE q] (h : p → q) (h' : ¬p → q) : q :=
  (Or'.em p).elim h h'

attribute [ccongr] and_congr
attribute [ccongr] not_congr

@[ccongr]
theorem iff_congr' {p₁ p₂ q₁ q₂} (hp : p₁ ↔ p₂) (hq : q₁ ↔ q₂) : (p₁ ↔ q₁) ↔ (p₂ ↔ q₂) := by
  constructor
  · intro h
    exact hp.symm.trans (h.trans hq)
  · intro h
    exact hp.trans (h.trans hq.symm)

@[cnsimp]
theorem or'_false [DNE p] : p ∨' False ↔ p := by
  constructor
  · intro h
    apply DNE.dne
    intro h'
    apply h
    exact ⟨h', not_false⟩
  · intro h
    exact .inl h

theorem or'_comm : p ∨' q ↔ q ∨' p :=
  not_congr and_comm

@[cnsimp]
theorem false_or' [DNE p] : False ∨' p ↔ p :=
  or'_comm.trans or'_false

@[cnsimp]
theorem or'_true : p ∨' True ↔ True := by
  constructor
  · intro h
    exact trivial
  · intro h
    exact .inr h

@[cnsimp]
theorem true_or' : True ∨' p ↔ True :=
  or'_comm.trans or'_true

@[ccongr]
theorem or'_congr (h₁ : p₁ ↔ p₂) (h₂ : q₁ ↔ q₂) : p₁ ∨' q₁ ↔ p₂ ∨' q₂ :=
  not_congr (and_congr (not_congr h₁) (not_congr h₂))

@[ccongr]
theorem exists'_congr {β₁ β₂ : α → Prop} (h : ∀ x, β₁ x ↔ β₂ x) : (∃' x, β₁ x) ↔ ∃' x, β₂ x :=
  not_congr (forall_congr' (fun x => not_congr (h x)))

@[cnsimp]
theorem exists'_false : (∃' _ : α, False) ↔ False := by
  apply iff_false_intro
  intro h
  exact h.elim fun _ h => h

@[cnsimp]
theorem true_and_iff : True ∧ p ↔ p := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨trivial, h⟩

@[cnsimp]
theorem and_true_iff : p ∧ True ↔ p :=
  and_comm.trans true_and_iff

@[cnsimp]
theorem false_and_iff : False ∧ p ↔ False := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact h.elim

@[cnsimp]
theorem and_false_iff : p ∧ False ↔ False :=
  and_comm.trans false_and_iff

@[cnsimp]
theorem not_true_iff : ¬True ↔ False :=
  ⟨fun h => h trivial, fun h => h.elim⟩

@[cnsimp]
theorem not_not [DNE p] : ¬¬p ↔ p :=
  ⟨DNE.dne, not_not_intro⟩

@[cnsimp]
theorem iff_self_iff_true : (p ↔ p) ↔ True :=
  iff_true_intro ⟨id, id⟩

@[cnsimp]
theorem and_self_iff' : p ∧ p ↔ p :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

@[cnsimp]
theorem or'_self_iff [DNE p] : p ∨' p ↔ p := by
  unfold Or'
  cnsimp

@[cnsimp]
theorem iff_true_iff : (p ↔ True) ↔ p :=
  ⟨of_iff_true, iff_true_intro⟩

@[cnsimp]
theorem iff_false_iff : (p ↔ False) ↔ ¬p :=
  ⟨fun h => h.1, iff_false_intro⟩

@[cnsimp]
theorem true_iff_iff : (True ↔ p) ↔ p :=
  iff_comm.trans iff_true_iff

@[cnsimp]
theorem false_iff_iff : (False ↔ p) ↔ ¬p :=
  iff_comm.trans iff_false_iff

attribute [cnsimp] true_imp_iff
attribute [cnsimp] imp_true_iff
attribute [cnsimp] false_imp_iff
attribute [cnsimp] imp_false
attribute [cnsimp] not_false_iff
attribute [cnsimp] and_not_self_iff
attribute [cnsimp] not_and_self_iff

@[cnsimp]
theorem not_or' : ¬(p ∨' q) ↔ ¬p ∧ ¬q := by
  unfold Or'
  exact not_not

theorem not_and_iff_not_or_not [DNE p] [DNE q] : ¬(p ∧ q) ↔ ¬p ∨' ¬q := by
  unfold Or'
  cnsimp

structure Prop' where
  p : Prop
  [dne : DNE p]

attribute [coe] Prop'.mk
attribute [instance] Prop'.dne

instance [DNE p] : CoeDep Prop p Prop' where
  coe := Prop'.mk p

instance : CoeSort Prop' Prop where
  coe := Prop'.p

class Eqv (α : Sort u) where
  eqv : α → α → Prop'
  refl x : eqv x x
  symm {x y} (h : eqv x y) : eqv y x
  trans {x y z} (h₁ : eqv x y) (h₂ : eqv y z) : eqv x z

instance [DecidableEq α] : Eqv α where
  eqv x y := x = y
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

def Eq' [Eqv α] (x y : α) : Prop := Eqv.eqv x y

infix:50 " ~= " => Eq'

def Ne' [Eqv α] (x y : α) : Prop := ¬x ~= y

infix:50 " ~!= " => Ne'

instance [Eqv α] (x y : α) [Decidable (x ~= y)] : Decidable (x ~!= y) :=
  if h : x ~= y then .isFalse (fun h' => h' h) else .isTrue h

@[cnsimp]
theorem ne'_iff [Eqv α] (x y : α) : x ~!= y ↔ ¬x ~= y := Iff.rfl

theorem Eq'.refl [Eqv α] (x : α) : x ~= x := Eqv.refl x
@[refl] theorem Eq'.rfl [Eqv α] {x : α} : x ~= x := Eqv.refl x
theorem Eq'.symm [Eqv α] {x y : α} (h : x ~= y) : y ~= x := Eqv.symm h
theorem Eq'.trans [Eqv α] {x y z : α} (h₁ : x ~= y) (h₂ : y ~= z) : x ~= z := Eqv.trans h₁ h₂

theorem Ne'.symm [Eqv α] {x y : α} (h : x ~!= y) : y ~!= x := mt Eq'.symm h

instance [Eqv α] : @Trans α α α (· ~= ·) (· ~= ·) (· ~= ·) := ⟨Eq'.trans⟩

@[ccongr]
theorem eq'_congr [Eqv α] {x₁ x₂ y₁ y₂ : α} (h₁ : x₁ ~= x₂) (h₂ : y₁ ~= y₂) : x₁ ~= y₁ ↔ x₂ ~= y₂ := by
  constructor
  · intro h
    exact h₁.symm.trans (h.trans h₂)
  · intro h
    exact h₁.trans (h.trans h₂.symm)

@[cnsimp]
theorem eq'_self_iff {x : α} [Eqv α] : x ~= x ↔ True :=
  iff_true_intro .rfl

instance [Eqv α] (x y : α) : DNE (x ~= y) := inferInstanceAs (DNE (Prop'.p _))

instance : Eqv Prop' where
  eqv a b := a ↔ b
  refl _ := .rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

@[ccongr]
theorem Prop'.p_congr {x y : Prop'} (h : x ~= y) : x.p ↔ y.p := h

@[ccongr]
theorem Prop'.mk_congr {x y : Prop} [DNE x] [DNE y] (h : x ↔ y) : Prop'.mk x ~= Prop'.mk y := h

@[cnsimp] theorem Prop'.mk_p (x : Prop') : Prop'.mk x.p ~= x := Iff.rfl

structure Fun (α : Sort u) (β : Sort v) [Eqv α] [Eqv β] where
  toFn : α → β
  congr {x y} (h : x ~= y) : toFn x ~= toFn y

run_elab
  Lean.Meta.registerCoercion ``Fun.toFn
    (some { numArgs := 5, coercee := 4, type := .coeFun })

infixr:35 " ~> " => Fun

macro "mk_fun_congr" : tactic =>
  `(tactic| (intro x y h; dsimp only; first | rfl | cases (h : _ = _); rfl | ccongr <;> exact h))

@[inline, always_inline]
def Fun.mkFun' {α : Sort u} {β : Sort v} [Eqv α] [Eqv β]
    (toFn : α → β) (congr : ∀ {x y}, x ~= y → toFn x ~= toFn y := by mk_fun_congr) : α ~> β :=
  ⟨toFn, congr⟩

@[inline, always_inline]
instance [Eqv α] [Eqv β] : CoeFun (α ~> β) (fun _ => α → β) := ⟨Fun.toFn⟩

instance {α : Sort u} {β : Sort v} [Eqv α] [Eqv β] : Eqv (α ~> β) where
  eqv x y := ∀ z, x.1 z ~= y.1 z
  refl _ := fun _ => .rfl
  symm h := fun z => (h z).symm
  trans h₁ h₂ := fun z => (h₁ z).trans (h₂ z)

@[ccongr]
theorem Fun.apply_congr [Eqv α] [Eqv β] {f₁ f₂ : α ~> β} {x₁ x₂ : α}
    (hf : f₁ ~= f₂) (hx : x₁ ~= x₂) : f₁ x₁ ~= f₂ x₂ :=
  (hf x₁).trans (f₂.congr hx)

theorem Fun.mkFun'_congr.proof {α : Sort u} {β : Sort v} {_ : Eqv α} {_ : Eqv β}
    {f₁ f₂ : α → β} (hf : ∀ x, f₁ x ~= f₂ x)
    (h₁ : ∀ {x y : α}, x ~= y → f₁ x ~= f₁ y) :
    ∀ (x y : α), x ~= y → f₂ x ~= f₂ y := by
  intro x y h
  cnsimp [← hf]
  exact h₁ h

@[ccongr]
theorem Fun.mkFun'_congr {α : Sort u} {β : Sort v} {_ : Eqv α} {_ : Eqv β}
    {f₁ f₂ : α → β} {h₁} (hf : ∀ x, f₁ x ~= f₂ x) :
    mkFun' f₁ h₁ ~= mkFun' f₂ @(Fun.mkFun'_congr.proof hf h₁) :=
  hf

@[cnsimp]
theorem Fun.apply_mkFun' [Eqv α] [Eqv β] {f : α → β} {h} {x} : Fun.mkFun' f h x ~= f x := by
  rfl

@[inline]
def Fun.id [Eqv α] : α ~> α := ⟨fun x => x, fun h => h⟩

@[cnsimp]
theorem Fun.id_eq [Eqv α] (x : α) : Fun.id x ~= x := by
  rfl

theorem funext' [Eqv α] [Eqv β] {f g : α ~> β} (h : ∀ x, f x ~= g x) : f ~= g := by
  exact h

macro:arg "fun'" x:ident " => " b:term : term => `(Fun.mkFun' (fun $x => $b))
macro:arg "fun'" x:ident " : " t:term " => " b:term : term => `(Fun.mkFun' (fun $x : $t => $b))

@[app_unexpander Fun.mkFun'] def unexpandFunMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $fn $(_)) =>
    match fn with
    | `(fun $x:ident => $b) => `(fun' $x:ident => $b)
    | _                     => throw ()
  | _                       => throw ()

macro "by_cases'" h:ident " : " t:term : tactic =>
  `(tactic| refine DNE.byCases (fun $h : $t => ?_) (fun $h => ?_))

def Noncomputable (α : Sort u) [Eqv α] := { x : α → Prop' // ∃' y, ∀ z, x z ↔ z ~= y }
def Noncomputable.mk [Eqv α] (x : α) : Noncomputable α := ⟨fun z => z ~= x, .intro x fun _ => .rfl⟩

def Noncomputable.uniqueChoice [Eqv α] (p : α ~> Prop') (h : ∃' x, p x ∧ ∀ y, p y → x ~= y) :
    Noncomputable α :=
  ⟨p, by
    refine h.elim fun x hx => ?_
    refine .intro x fun y => ?_
    constructor
    · intro h'
      exact (hx.2 y h').symm
    · intro h'
      cnsimp [h', hx.1]⟩

@[cnsimp]
def Noncomputable.val_mk [Eqv α] (x y : α) : (mk x).val y ↔ y ~= x := Iff.rfl

instance {inst : Eqv α} : Eqv (Noncomputable α) where
  eqv x y := ∀ z, x.1 z ↔ y.1 z
  refl _ := fun _ => .rfl
  symm h := fun z => (h z).symm
  trans h₁ h₂ := fun z => (h₁ z).trans (h₂ z)

theorem Noncomputable.exists_eq'_mk [Eqv α] (t : Noncomputable α) : ∃' y, t ~= mk y := t.2

theorem Noncomputable.elim [Eqv α] {p : Prop} [DNE p]
    (t : Noncomputable α) (h : ∀ a, t ~= mk a → p) : p := t.2.elim h

@[elab_as_elim]
theorem Noncomputable.ind [Eqv α] {motive : Noncomputable α → Prop} [∀ a, DNE (motive a)]
    (mk : ∀ t a, t ~= mk a → motive t) (t : Noncomputable α) : motive t := t.elim (mk t)

@[ccongr]
theorem Noncomputable.val_congr [Eqv α] {x₁ x₂ : Noncomputable α} {y₁ y₂ : α}
    (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : x₁.val y₁ ~= x₂.val y₂ := by
  dsimp [Eq', Eqv.eqv] at hx
  dsimp [Eq', Eqv.eqv]
  cnsimp only [hx]
  refine x₂.2.elim (fun a ha => ?_)
  cnsimp only [ha]
  cnsimp [hy]

@[ccongr]
theorem Noncomputable.mk_congr [Eqv α] {x y : α} (h : x ~= y) : mk x ~= mk y := by
  intro z
  unfold mk
  dsimp
  exact eq'_congr .rfl h

@[cnsimp]
theorem Noncomputable.mk_inj [Eqv α] {x y : α} : mk x ~= mk y ↔ x ~= y := by
  constructor
  · intro h
    dsimp only [mk] at h
    specialize h x
    exact h.mp .rfl
  · exact Noncomputable.mk_congr

def Noncomputable.uniqueChoice' [Eqv α] (p : Noncomputable α ~> Prop') (h : ∃' x, p x ∧ ∀ y, p y → x ~= y) :
    Noncomputable α :=
  ⟨fun x => p (mk x), by
    refine h.elim fun x hx => ?_
    refine x.elim fun a ha => ?_
    refine .intro a fun y => ?_
    dsimp
    cnsimp [ha] at hx
    constructor
    · intro h'
      exact Noncomputable.mk_inj.mp (hx.2 (mk y) h').symm
    · intro h'
      cnsimp [h', hx]⟩

def Noncomputable.ite {α : Sort u} [Eqv α] (p : Prop) (t e : Noncomputable α) : Noncomputable α :=
  ⟨fun x => (p ∧ t.1 x) ∨' (¬p ∧ e.1 x), by
    dsimp
    by_cases' h : p
    · refine t.elim (fun x hx => ?_)
      refine .intro x ?_
      intro z
      cnsimp [h, hx]
    · refine e.elim (fun x hx => ?_)
      refine .intro x ?_
      intro z
      cnsimp [h, hx]⟩

@[ccongr]
theorem Noncomputable.ite_congr {inst : Eqv α} {p₁ p₂ : Prop} {t₁ t₂ e₁ e₂ : Noncomputable α}
    (hp : p₁ ↔ p₂) (ht : t₁ ~= t₂) (he : e₁ ~= e₂) : ite p₁ t₁ e₁ ~= ite p₂ t₂ e₂ := by
  intro z
  unfold ite
  dsimp
  ccongr <;> assumption

@[cnsimp]
theorem Noncomputable.ite_true {inst : Eqv α} {t e : Noncomputable α} : ite True t e ~= t := by
  intro z
  dsimp [ite]
  cnsimp

@[cnsimp]
theorem Noncomputable.ite_false {inst : Eqv α} {t e : Noncomputable α} : ite False t e ~= e := by
  intro z
  dsimp [ite]
  cnsimp

attribute [cnsimp] Noncomputable.ite_false

theorem Noncomputable.ite_pos [Eqv α] {x : Prop} (h : x) {t e : Noncomputable α} :
    ite x t e ~= t := by
  cnsimp [h]

theorem Noncomputable.ite_neg [Eqv α] {x : Prop} (h : ¬x) {t e : Noncomputable α} :
    ite x t e ~= e := by
  cnsimp [h]

def Noncomputable.test [Eqv α] (x : Noncomputable α) (p : α ~> Prop') : Prop' :=
  ∀ a, x.1 a → p a

@[ccongr]
theorem Noncomputable.test_congr [Eqv α] {x₁ x₂ : Noncomputable α} {p₁ p₂ : α ~> Prop'}
    (hx : x₁ ~= x₂) (hp : p₁ ~= p₂) : x₁.test p₁ ~= x₂.test p₂ := by
  dsimp only [test]
  cnsimp only [hx, hp, eq'_self_iff]

@[cnsimp]
theorem Noncomputable.test_mk [Eqv α] (x : α) (p : α ~> Prop') : (mk x).test p ~= p x := by
  dsimp only [test, mk]
  constructor
  · intro h
    exact h x .rfl
  · intro h a ha
    cnsimp only [ha, h]

def Noncomputable.bind [Eqv α] [Eqv β] (x : Noncomputable α) (f : α ~> Noncomputable β) : Noncomputable β :=
  ⟨fun y => x.test (fun' a => (f a).1 y), by
    refine x.elim fun y hy => ?_
    refine (f y).elim fun z hz => ?_
    dsimp
    cnsimp only [hy, test_mk, Fun.apply_mkFun']
    refine .intro z ?_
    cnsimp [hz]⟩

@[ccongr]
theorem Noncomputable.bind_congr [Eqv α] [Eqv β] {x₁ x₂ : Noncomputable α} {f₁ f₂ : α ~> Noncomputable β}
    (hx : x₁ ~= x₂) (hf : f₁ ~= f₂) : x₁.bind f₁ ~= x₂.bind f₂ := by
  unfold bind
  intro z
  dsimp
  ccongr <;> assumption

@[cnsimp]
theorem Noncomputable.bind_mk [Eqv α] [Eqv β] (x : α) (f : α ~> Noncomputable β) :
    (mk x).bind f ~= f x := by
  intro y
  dsimp only [bind]
  cnsimp

def Noncomputable.map [Eqv α] [Eqv β] (f : α ~> β) (x : Noncomputable α) : Noncomputable β :=
  x.bind (fun' y => mk (f y))

@[ccongr]
theorem Noncomputable.map_congr [Eqv α] [Eqv β] {f₁ f₂ : α ~> β} {x₁ x₂ : Noncomputable α}
    (hf : f₁ ~= f₂) (hx : x₁ ~= x₂) : map f₁ x₁ ~= map f₂ x₂ := by
  dsimp only [map]
  ccongr <;> assumption

@[cnsimp]
theorem Noncomputable.map_mk [Eqv α] [Eqv β] (f : α ~> β) (x : α) : map f (mk x) ~= mk (f x) := by
  dsimp only [map]
  cnsimp

def Noncomputable.liftProp (x : Noncomputable Prop') : Prop' := x.test .id

@[ccongr]
theorem Noncomputable.liftProp_congr {x₁ x₂ : Noncomputable Prop'} (h : x₁ ~= x₂) : liftProp x₁ ~= liftProp x₂ := by
  dsimp only [liftProp]
  ccongr <;> assumption

@[cnsimp]
theorem Noncomputable.liftProp_mk (x : Prop') : liftProp (mk x) ~= x := by
  dsimp only [liftProp]
  cnsimp

@[cnsimp]
theorem Noncomputable.mk_liftProp (x : Noncomputable Prop') : mk (liftProp x) ~= x := by
  refine x.elim fun y hy => ?_
  dsimp only [liftProp]
  cnsimp [hy]

example (x : Prop) [DNE x] : x ↔ (¬((False ↔ False) ∧ (x ↔ True)) ↔ False) := by
  cnsimp

def t :=
  ((((Noncomputable.mk (True : Prop')).map (fun' x => Noncomputable.mk x))).map
    (fun' x => x.liftProp)).liftProp

example : t ~= True := by
  unfold t
  cnsimp

def Nonempty' (α : Sort u) : Prop := ¬(α → False)

instance : DNE (Nonempty' α) := inferInstanceAs (DNE ¬_)

theorem Nonempty'.intro (x : α) : Nonempty' α := by
  intro h
  exact h x

theorem Nonempty'.elim [DNE p] (h : Nonempty' α) (intro : α → p) : p := by
  apply DNE.dne
  intro h'
  apply h
  intro x
  exact h' (intro x)


class Setoid' (α : Sort u) [Eqv α] where
  r : α → α → Prop'
  of_eq' : x ~= y → r x y
  symm : r x y → r y x
  trans : r x y → r y z → r x z

theorem Setoid'.rfl {_ : Eqv α} [s : Setoid' α] {x : α} : s.r x x :=
  Setoid'.of_eq' .rfl

instance [Eqv α] [Setoid' α] : HasEquiv α where
  Equiv x y := Setoid'.r x y

inductive Quotient' [Eqv α] : (s : Setoid' α) → Sort _ where
  | mk (s) (a : α) : Quotient' s

instance {_ : Eqv α} {s : Setoid' α} : Eqv (Quotient' s) where
  eqv x y := s.r x.1 y.1
  refl _ := Setoid'.rfl
  symm := Setoid'.symm
  trans := Setoid'.trans

/--
Low-level function to extract the value out of a quotient.
This function is "unsafe" because it breaks congruence.
Use `lift` instead for nicer congruence for rewriting.
-/
abbrev Quotient'.unquot [Eqv α] [Eqv β] {s : Setoid' α} (q : Quotient' s) : α := q.1

@[inline, always_inline]
def Quotient'.lift [Eqv α] [Eqv β] {s : Setoid' α} (f : α ~> β) :
    (∀ x y, x ≈ y → f x ~= f y) → Quotient' s → β
  | _, mk _ a => f a

theorem Quotient'.ind [Eqv α] {s : Setoid' α}
    {motive : Quotient' s → Prop} (mk : ∀ a, motive (mk s a))
    (t : Quotient' s) : motive t :=
  mk t.1

theorem Quotient'.sound [Eqv α] [Eqv β] {s : Setoid' α} {a b : α} :
    a ≈ b → mk s a ~= mk s b := id

theorem Quotient'.exact [Eqv α] [Eqv β] {s : Setoid' α} {a b : α} :
    mk s a ~= mk s b → a ≈ b := id

@[ccongr]
theorem Quotient'.mk_congr [Eqv α] {s : Setoid' α} {a b : α}
    (h : a ~= b) : Quotient'.mk s a ~= Quotient'.mk s b :=
  Setoid'.of_eq' h

set_option linter.unusedVariables false in
private theorem Quotient'.translate_lift [Eqv α] [Eqv β]
    {f₁ f₂ : α ~> β} (hf : f₁ ~= f₂) {s : Setoid' α}
    (h₁ : ∀ (x y : α), x ≈ y → f₁ x ~= f₁ y) :
    ∀ (x y : α), x ≈ y → f₂ x ~= f₂ y := by
  intro x y h
  specialize h₁ x y h
  cnsimp [← hf, h₁]

@[ccongr]
theorem Quotient'.lift_congr [Eqv α] [Eqv β] {s : Setoid' α}
    {f₁ f₂ : α ~> β} (hf : f₁ ~= f₂)
    {h₁}
    {h₂ : optParam (∀ (x y : α), x ≈ y → f₂ x ~= f₂ y) (translate_lift hf h₁)}
    {q₁ q₂ : Quotient' s}
    (hq : q₁ ~= q₂) :
    q₁.lift f₁ h₁ ~= q₂.lift f₂ h₂ :=
  (hf q₁.1).trans (h₂ _ _ hq)

def Setoid'.trueSetoid (α : Sort u) [Eqv α] : Setoid' α where
  r _ _ := True
  of_eq' _ := trivial
  symm h := h
  trans h _ := h

abbrev Squash' (α : Sort u) [Eqv α] := Quotient' (Setoid'.trueSetoid α)

inductive EqvGenPath {α : Sort u} [Eqv α] (r : α → α → Prop) : α → α → Sort _ where
  | rel {x y : α} (h : r x y) : EqvGenPath r x y
  | of_eq' {x y : α} (h : x ~= y) : EqvGenPath r x y
  | symm {x y : α} (h : EqvGenPath r x y) : EqvGenPath r y x
  | trans {x y z : α} (h : EqvGenPath r x y) (h' : EqvGenPath r y z) : EqvGenPath r x z

def EqvGen' {α : Sort u} [Eqv α] (r : α → α → Prop) (x y : α) : Prop :=
  Nonempty' (EqvGenPath r x y)

instance [Eqv α] (r : α → α → Prop) : DNE (EqvGen' r x y) := inferInstanceAs (DNE ¬_)

theorem EqvGen'.rel [Eqv α] {x y : α} (h : r x y) : EqvGen' r x y :=
  .intro (.rel h)

theorem EqvGen'.of_eq' [Eqv α] {x y : α} (h : x ~= y) : EqvGen' r x y :=
  .intro (.of_eq' h)

theorem EqvGen'.refl [Eqv α] (x : α) : EqvGen' r x x :=
  .of_eq' .rfl

theorem EqvGen'.rfl [Eqv α] {x : α} : EqvGen' r x x :=
  .of_eq' .rfl

theorem EqvGen'.symm [Eqv α] {x y : α} (h : EqvGen' r x y) : EqvGen' r y x :=
  h.elim (fun e => .intro e.symm)

theorem EqvGen'.trans [Eqv α] {x y z : α}
    (h : EqvGen' r x y) (h' : EqvGen' r y z) : EqvGen' r x z :=
  h.elim (fun e => h'.elim (fun e' => .intro (e.trans e')))

@[ccongr]
theorem EqvGen'.congr [Eqv α] {x₁ x₂ y₁ y₂ : α}
    (hx : x₁ ~= x₂) (hy : y₁ ~= y₂) : EqvGen' r x₁ y₁ ↔ EqvGen' r x₂ y₂ := by
  constructor
  · intro h
    exact (of_eq' hx.symm).trans (h.trans (of_eq' hy))
  · intro h
    exact (of_eq' hx).trans (h.trans (of_eq' hy.symm))

theorem EqvGen'.ind
    [Eqv α] {motive : α → α → Prop} [∀ x y, DNE (motive x y)]
    (rel : ∀ {x y}, r x y → motive x y)
    (of_eq' : ∀ {x y}, x ~= y → motive x y)
    (symm : ∀ {x y}, EqvGen' r x y → motive x y → motive y x)
    (trans : ∀ {x y z}, EqvGen' r x y → EqvGen' r y z → motive x y → motive y z → motive x z)
    (h : EqvGen' r x y) : motive x y := by
  apply h.elim fun path => ?_
  clear h
  induction path with
  | rel h => exact rel h
  | of_eq' h => exact of_eq' h
  | symm h ih => exact symm (.intro h) ih
  | trans h h' ih ih' => exact trans (.intro h) (.intro h') ih ih'

--set_option pp.explicit true in

/-
run_meta
  let a := CCongr.ccongrExtension.getState (← Lean.getEnv)
  let a := a.lemmas.find! { rel := ``Eq', decl := ``Quotient'.lift }
  Lean.logInfo m!"{reprPrec a 0}"
-/

--set_option trace.Meta.Tactic.simp true


def testing :
    (fun' x : Prop' => (x ↔ True : Prop')) ~= (fun' x => x) := by
  ccongr
  cnsimp only [iff_true_iff, eq'_self_iff]

example (x y : Fun Prop' Prop') (h : x ~= y) : x ~= y := by
  cnsimp [h]

instance [Eqv α] [Eqv β] : Eqv (α × β) where
  eqv x y := x.1 ~= y.1 ∧ x.2 ~= y.2
  refl _ := ⟨.rfl, .rfl⟩
  symm h := ⟨h.1.symm, h.2.symm⟩
  trans h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

@[cnsimp]
theorem Prod.mk.inj'_iff [Eqv α] [Eqv β] {x₁ x₂ : α} {y₁ y₂ : β} :
    (x₁, y₁) ~= (x₂, y₂) ↔ x₁ ~= x₂ ∧ y₁ ~= y₂ := Iff.rfl

instance [Eqv α] [Eqv β] : Eqv (α ×' β) where
  eqv x y := x.1 ~= y.1 ∧ x.2 ~= y.2
  refl _ := ⟨.rfl, .rfl⟩
  symm h := ⟨h.1.symm, h.2.symm⟩
  trans h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

@[cnsimp]
theorem PProd.mk.inj'_iff {α β} [Eqv α] [Eqv β] {x₁ x₂ : α} {y₁ y₂ : β} :
    ⟨x₁, y₁⟩ ~= (⟨x₂, y₂⟩ : α ×' β) ↔ x₁ ~= x₂ ∧ y₁ ~= y₂ := Iff.rfl

instance [Eqv α] [Eqv β] : Eqv (α ⊕ β) where
  eqv
  | .inl x, .inl y => x ~= y
  | .inr x, .inr y => x ~= y
  | _, _ => False
  refl
  | .inl _ => .rfl
  | .inr _ => .rfl
  symm {x y} h :=
    match x, y with
    | .inl _, .inl _ => h.symm
    | .inr _, .inr _ => h.symm
    | .inl _, .inr _ => h
    | .inr _, .inl _ => h
  trans {x y z} h h' :=
    match x, y, z with
    | .inl _, .inl _, .inl _ => h.trans h'
    | .inr _, .inr _, .inr _ => h.trans h'
    | .inl _, .inr _, _ => h.elim
    | .inr _, .inl _, _ => h.elim

@[cnsimp]
theorem Sum.inl.inj'_iff [Eqv α] [Eqv β] {x₁ x₂ : α} :
    .inl x₁ ~= (.inl x₂ : α ⊕ β) ↔ x₁ ~= x₂ := Iff.rfl

@[cnsimp]
theorem Sum.inr.inj'_iff [Eqv α] [Eqv β] {x₁ x₂ : β} :
    .inr x₁ ~= (.inr x₂ : α ⊕ β) ↔ x₁ ~= x₂ := Iff.rfl

@[cnsimp]
theorem Sum.inl_eq'_inr [Eqv α] [Eqv β] {x₁ : α} {x₂ : β} :
    .inl x₁ ~= (.inr x₂ : α ⊕ β) ↔ False := Iff.rfl

@[cnsimp]
theorem Sum.inr_eq'_inl [Eqv α] [Eqv β] {x₁ : β} {x₂ : α} :
    .inr x₁ ~= (.inl x₂ : α ⊕ β) ↔ False := Iff.rfl

instance [Eqv α] [Eqv β] : Eqv (α ⊕' β) where
  eqv
  | .inl x, .inl y => x ~= y
  | .inr x, .inr y => x ~= y
  | _, _ => False
  refl
  | .inl _ => .rfl
  | .inr _ => .rfl
  symm {x y} h :=
    match x, y with
    | .inl _, .inl _ => h.symm
    | .inr _, .inr _ => h.symm
    | .inl _, .inr _ => h
    | .inr _, .inl _ => h
  trans {x y z} h h' :=
    match x, y, z with
    | .inl _, .inl _, .inl _ => h.trans h'
    | .inr _, .inr _, .inr _ => h.trans h'
    | .inl _, .inr _, _ => h.elim
    | .inr _, .inl _, _ => h.elim

@[cnsimp]
theorem PSum.inl.inj'_iff [Eqv α] [Eqv β] {x₁ x₂ : α} :
    .inl x₁ ~= (.inl x₂ : α ⊕' β) ↔ x₁ ~= x₂ := Iff.rfl

@[cnsimp]
theorem PSum.inr.inj'_iff [Eqv α] [Eqv β] {x₁ x₂ : β} :
    .inr x₁ ~= (.inr x₂ : α ⊕' β) ↔ x₁ ~= x₂ := Iff.rfl

@[cnsimp]
theorem PSum.inl_eq'_inr [Eqv α] [Eqv β] {x₁ : α} {x₂ : β} :
    .inl x₁ ~= (.inr x₂ : α ⊕' β) ↔ False := Iff.rfl

@[cnsimp]
theorem PSum.inr_eq'_inl [Eqv α] [Eqv β] {x₁ : β} {x₂ : α} :
    .inr x₁ ~= (.inl x₂ : α ⊕' β) ↔ False := Iff.rfl
