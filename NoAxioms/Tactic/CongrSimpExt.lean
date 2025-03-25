import Lean.Meta.Tactic.Simp

open Lean Meta

namespace Lean.Expr

private def getAppArgsAux' : Expr → Array Expr → Nat → Array Expr
  | app f a, as, i => getAppArgsAux' f (as.set! i a) (i-1)
  | mdata _ e, as, i => getAppArgsAux' e as i
  | _,       as, _ => as

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` -/
@[inline] def getAppArgs' (e : Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs'
  getAppArgsAux' e (Array.replicate nargs dummy) (nargs-1)

end Lean.Expr

def Lean.Level.isAlwaysZero : Level → Bool
  | .zero ..    => true
  | .mvar ..    => false
  | .param ..   => false
  | .succ ..    => false
  | .max u v    => isAlwaysZero u && isAlwaysZero v
  | .imax _ u   => isAlwaysZero u

initialize cnsimpExt : SimpExtension
  ← mkSimpExt

namespace CnSimp

@[inline]
def checkIsRel (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match type with
  | mkApp2 rel lhs rhs =>
    let r := rel.getAppFn'
    unless r.isConst do
      return none
    if ((← getEnv).find? (.str r.constName! "trans")).isSome then
      return some (rel, lhs, rhs)
    return none
  | _ => pure none

end CnSimp

namespace CCongr

theorem forall_prop_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₁ → Prop}
    (hp : p₁ ↔ p₂) (hq : ∀ h, q₁ h ↔ q₂ h) :
    (∀ h, q₁ h) ↔ (∀ h, q₂ (hp.mpr h)) := by
  constructor
  · intro h' x
    exact (hq (hp.mpr x)).mp (h' (hp.mpr x))
  · intro h' x
    exact (hq x).mpr (h' (hp.mp x))

theorem forall_prop_dom_congr {p₁ p₂ : Prop} {q : p₁ → Prop}
    (hp : p₁ ↔ p₂) : (∀ h, q h) ↔ (∀ h, q (hp.mpr h)) := by
  exact forall_prop_congr hp (fun _ => .rfl)

structure CCongrKey where
  rel : Name
  decl : Name
deriving Inhabited, Repr, DecidableEq, Hashable

inductive ParameterDischarger where
  | none
  | synth (type : Expr)
  | exact (expr : Expr)
deriving Inhabited, Repr

inductive ParameterFillOutProcedure where
  /--
  A fixed parameter that doesn't change between the lhs and rhs.
  `i` indexes into the parameters of the function.
  -/
  | fixed (i : Nat)
  /--
  A parameter that is only present on the lhs.
  -/
  | preParam (i : Nat)
  /--
  A parameter that is only present on the rhs.
  `discharge` determines whether the parameter needs to be determined through
  e.g. instance synthesis.
  -/
  | postParam (i : Nat) (disch : ParameterDischarger)
  /--
  A relation hypothesis to fill out (e.g. `a ↔ b`).
  `rel` and `lhs` are expressions to be instantiated with bound variables from
  the parameters of the function.
  -/
  | rel (rel : Expr) (i : Nat)
deriving Inhabited, Repr

structure SimpleCCongrProcedure where
  /--
  The amount of parameters (implicit and explicit) that the function at `funName` takes.
  -/
  arity : Nat
  /--
  How to derive the level parameters to provide to the theorem declaration.
  The entry `lparamPerm[i]` where `i` is the index of the parameter in `thmName`
  represents the index of the parameter in the function application of `funName`.
  -/
  lparamPerm : List Nat
  /--
  The meaning of every parameter in the theorem.
  -/
  params : Array ParameterFillOutProcedure
deriving Inhabited, Repr

inductive Procedure where
  | expensiveProcedure (hypothesesPos : Array Nat)
  | simpleProcedure (thm : SimpleCCongrProcedure)
deriving Inhabited, Repr

structure CCongrTheorem where
  rel : Name -- name of the relation
  funName : Name
  thmName : Name
  priority  : Nat
  procedure : Procedure
deriving Inhabited, Repr

def CCongrTheorem.toKey (x : CCongrTheorem) : CCongrKey :=
  {
    rel := x.rel
    decl := x.funName
  }

structure CCongrTheorems where
  lemmas : SMap CCongrKey (List CCongrTheorem) := {}
  deriving Inhabited, Repr

def CCongrTheorems.insert (d : CCongrTheorems) (e : CCongrTheorem) : CCongrTheorems :=
  { d with lemmas :=
        match d.lemmas.find? e.toKey with
        | none    => d.lemmas.insert e.toKey [e]
        | some es => d.lemmas.insert e.toKey <| insert es }
where
  insert : List CCongrTheorem → List CCongrTheorem
    | []     => [e]
    | e'::es => if e.priority ≥ e'.priority then e::e'::es else e' :: insert es

initialize ccongrExtension : SimpleScopedEnvExtension CCongrTheorem CCongrTheorems ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := CCongrTheorems.insert
    finalizeImport := fun s => { s with lemmas := s.lemmas.switch }
  }

def mkCCongrTheorem (declName : Name) (prio : Nat) : MetaM CCongrTheorem := withReducible do
  let some c := (← getEnv).findConstVal? declName | throwError "unknown constant '{.ofConstName declName}'"
  let (xs, bis, type) ← forallMetaTelescopeReducing c.type
  let mkApp2 rel lhs rhs := type | throwError "invalid 'ccongr' theorem, relation application expected{indentExpr type}"
  let some relName := rel.getAppFn.constName? | throwError "invalid 'ccongr' theorem, relation application expected{indentExpr type}"

  lhs.withApp fun lhsFn lhsArgs => rhs.withApp fun rhsFn rhsArgs => do
    unless lhsFn.isConst && rhsFn.isConst && lhsFn.constName! == rhsFn.constName! && lhsArgs.size == rhsArgs.size do
      throwError "invalid 'ccongr' theorem, left/right-hand sides must be applications of the same function{indentExpr type}"
    let mut foundMVars : MVarIdSet := {}
    for lhsArg in lhsArgs do
      for mvarId in (lhsArg.collectMVars {}).result do
        foundMVars := foundMVars.insert mvarId
    let mut i : Nat := 0
    let mut hypothesesPos := #[]
    for x in xs, bi in bis do
      if bi.isExplicit && !foundMVars.contains x.mvarId! then
        let rhsFn? ← forallTelescopeReducing (← inferType x) fun ys xType => do
          let mkApp2 rel' xLhs xRhs := xType | return none
          let some _ := rel'.getAppFn.constName? | return none
          let mut j : Nat := 0
          for y in ys do
            let yType ← inferType y
            unless onlyMVarsAt yType foundMVars do
              throwError "invalid 'ccongr' theorem, argument #{j+1} of parameter #{i+1} contains unresolved parameter{indentExpr yType}"
            j := j + 1
          unless onlyMVarsAt xLhs foundMVars do
            throwError "invalid 'ccongr' theorem, parameter #{i+1} is not a valid hypothesis, the left-hand-side contains unresolved parameters{indentExpr xLhs}"
          let xRhsFn := xRhs.getAppFn
          unless xRhsFn.isMVar do
            throwError "invalid 'ccongr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side head is not a metavariable{indentExpr xRhs}"
          unless !foundMVars.contains xRhsFn.mvarId! do
            throwError "invalid 'ccongr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side head was already resolved{indentExpr xRhs}"
          for arg in xRhs.getAppArgs do
            unless arg.isFVar do
              throwError "invalid 'ccongr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side argument is not a local variable{indentExpr xRhs}"
          pure (some xRhsFn)
        match rhsFn? with
        | none       => pure ()
        | some rhsFn =>
          foundMVars    := foundMVars.insert x.mvarId! |>.insert rhsFn.mvarId!
          hypothesesPos := hypothesesPos.push i
      i := i + 1
    return {
      rel           := relName
      thmName       := declName
      funName       := lhsFn.constName!
      procedure     := .expensiveProcedure hypothesesPos
      priority      := prio
    }
where
  /-- Return `true` if `t` contains no metavariables that are not in `mvarSet` -/
  onlyMVarsAt (t : Expr) (mvarSet : MVarIdSet) : Bool :=
    Option.isNone <| t.find? fun e => e.isMVar && !mvarSet.contains e.mvarId!

def deriveLevelParamPerm (lhsFn : Expr) (lparams : List Name) : MetaM (List Nat × (Name → Option Level)) := do
  let levels := lhsFn.constLevels!
  if levels.length != lparams.length then
    throwError "invalid simple 'ccongr', level params should be permutations"
  let mut array := Array.replicate lparams.length 0
  let mut i := 0
  let mut map : NameMap Nat := ∅
  for l in levels do
    let .param name := l | throwError "invalid simple 'ccongr', theorem has non-param level {l}"
    let some idx := lparams.idxOf? name | throwError "invalid simple 'ccongr', invalid lparam"
    array := array.setIfInBounds idx i
    map := map.insert name i
    i := i + 1
  return (array.toList, fun n => (map.find? n).map (fun i => .param (.num .anonymous i)))

def mkSimpleCCongrTheorem (declName : Name) (prio : Nat) : MetaM CCongrTheorem := withReducible do
  let some c := (← getEnv).findConstVal? declName | throwError "unknown constant '{.ofConstName declName}'"
  let (xs, _, type) ← forallMetaTelescopeReducing c.type
  let mkApp2 rel lhs rhs := type | throwError "invalid 'ccongr' theorem, relation application expected{indentExpr type}"
  let some relName := rel.getAppFn.constName? | throwError "invalid 'ccongr' theorem, relation application expected{indentExpr type}"

  lhs.withApp fun lhsFn lhsArgs => rhs.withApp fun rhsFn rhsArgs => do
    unless lhsFn.isConst && rhsFn.isConst && lhsFn.constName! == rhsFn.constName! && lhsArgs.size == rhsArgs.size do
      throwError "invalid 'ccongr' theorem, left/right-hand sides must be applications of the same function{indentExpr type}"
    let (lperm, lfun) ← deriveLevelParamPerm lhsFn c.levelParams
    let mut params := #[]
    let mut mvarIdToPurpose : MVarIdMap ParameterFillOutProcedure := ∅
    let mut i := 0
    for x in lhsArgs do
      unless x.isMVar do
        throwError "invalid simple 'ccongr', fixed parameters ({x}) are not allowed"
      mvarIdToPurpose := mvarIdToPurpose.insert x.mvarId! (.preParam i)
      i := i + 1
    i := 0
    for x in rhsArgs do
      unless x.isMVar do
        throwError "invalid simple 'ccongr', fixed parameters ({x}) are not allowed"
      if mvarIdToPurpose.contains x.mvarId! then
        mvarIdToPurpose := mvarIdToPurpose.insert x.mvarId! (.fixed i)
      else
        let type ← x.mvarId!.getType
        mvarIdToPurpose := mvarIdToPurpose.insert x.mvarId! (.postParam i (.synth type))
      i := i + 1
    for x in xs do
      let mvar := x.mvarId!
      if let some val := mvarIdToPurpose.find? mvar then
        match val with
        | .postParam pos _ =>
          -- hack: store postParams as mvarIds to process later
          params := params.push (.postParam pos (.exact x))
        | _ => params := params.push val
      else
        let type ← mvar.getType'
        let some (rel, lhs, rhs) ← CnSimp.checkIsRel type |
          mvarIdToPurpose := mvarIdToPurpose.insert mvar (.postParam rhsArgs.size (.synth type))
          params := params.push (.postParam rhsArgs.size (.exact x))
          continue
        unless lhs.isMVar && rhs.isMVar do
          throwError "invalid simple 'ccongr', not parameters {type} {lhs} {rhs}"
        let some (.preParam pos) := mvarIdToPurpose.find? lhs.mvarId! |
          throwError "invalid simple 'ccongr', couldn't find lhs {lhs}"
        let some (.postParam pos' _) := mvarIdToPurpose.find? rhs.mvarId! |
          throwError "invalid simple 'ccongr', couldn't find rhs {rhs}"
        mvarIdToPurpose := mvarIdToPurpose.insert rhs.mvarId! (.postParam pos' .none)
        if pos != pos' then
          throwError "invalid simple 'ccongr', mismatch of positions"
        let rel' := (rel.abstract lhsArgs).instantiateLevelParamsCore lfun
        params := params.push (.rel rel' pos)
    params := params.mapIdx (fun
      | idx, .postParam _ (.exact (.mvar mvar)) =>
        let procedure := mvarIdToPurpose.find! mvar
        match procedure with
        | .postParam pos (.synth type) =>
          let type := (type.abstract (xs.take idx)).instantiateLevelParamsCore lfun
          if type.isOptParam then
            .postParam pos (.exact type.appArg!)
          else
            .postParam pos (.synth type)
        | _ => procedure
      | _, x => x)
    return {
      rel           := relName
      thmName       := declName
      funName       := lhsFn.constName!
      procedure     := .simpleProcedure {
        arity         := lhsArgs.size
        lparamPerm    := lperm
        params        := params
      }
      priority := prio
    }

def addCCongrTheorem (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  try
    let lemma ← mkSimpleCCongrTheorem declName prio
    ccongrExtension.add lemma attrKind
  catch e =>
    Lean.logInfo m!"{e.toMessageData}"
    let lemma ← mkCCongrTheorem declName prio
    ccongrExtension.add lemma attrKind

/--
Marks congruence theorems for cnsimp.
-/
initialize
  registerBuiltinAttribute {
    name  := `ccongr
    descr := "congruence theorem for cnsimp"
    add   := fun declName stx attrKind => do
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addCCongrTheorem declName attrKind prio |>.run {} {}
  }

end CCongr

namespace CnSimp

partial def preprocess (e type : Expr) (inv : Bool) : MetaM (List (Expr × Expr)) :=
  withReducible (go e type)
where
  go (e type : Expr) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  let type := type.consumeMData
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← go e type
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if let some p := type.not? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type := mkIff p (mkConst ``False)
    let e    := mkApp2 (mkConst ``iff_false_intro) p e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← go e₁ type₁) ++ (← go e₂ type₂)
  else if let some (rel, lhs, rhs) ← checkIsRel type then
    if inv then
      let type := mkApp2 rel rhs lhs
      let relName := rel.getAppFn'.constName!
      let e ← mkAppM (.str relName "symm") #[e]
      return [(e, type)]
    else
      return [(e, type)]
  else
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'True'"
    let p    := type
    let type := mkIff p (mkConst ``True)
    let e    := mkApp2 (mkConst ``iff_true_intro) p e
    return [(e, type)]

def mkSimpTheoremCore (e lhs : Expr) (origin : Origin) (post : Bool := true) : MetaM SimpTheorem := do
  return {
    post := post
    proof := e
    origin := origin
    rfl := false
    keys := ← DiscrTree.mkPath lhs
  }

def mkSimpTheoremConst (c : Name) (post : Bool := true) (inv : Bool := false) : MetaM (List SimpTheorem) := withReducible do
  let some val := (← getEnv).findConstVal? c | throwError "unknown constant '{c}'"
  let type := val.type
  if inv then
    let proof : Expr := .const c (val.levelParams.map Level.param)
    let origin := .decl c post inv
    (← preprocess proof type true).mapM (fun (proof, lhs) => mkSimpTheoremCore proof lhs origin post)
  else
    let (_, _, e) ← forallMetaTelescopeReducing type
    let mkApp2 _ lhs _ := e | throwError "must be relation blah"
    let proof := .const c []
    let origin := .decl c post inv
    return [← mkSimpTheoremCore proof lhs origin post]

syntax (name := attrCnsimp) "cnsimp" : attr

initialize
  registerBuiltinAttribute {
    name  := `attrCnsimp
    descr := "cnsimp theorems"
    add   := fun declName stx attrKind => do
      let thms ← mkSimpTheoremConst declName |>.run' {} {}
      thms.forM (fun x => cnsimpExt.add (.thm x))
  }

end CnSimp
