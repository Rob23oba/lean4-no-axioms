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
  A parameter of the relation application.
  -/
  | relParam (i : Nat)
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

inductive CongrAssignmentType where
  /-- Assign the `i`th parameter of the proof. -/
  | assign (i : Nat)
  /-- Similar to `take` but with a defeq check. -/
  | take (i : Nat)
  /-- Don't do anything. -/
  | ignore
  deriving Inhabited, Repr

inductive CongrActionType where
  /--
  Introduce a meta-variable for the `i`th parameter of the proof
  (for instance synthesization).
  `type` represents the type of the meta-variable, with parameters abstracted
  and level parameters described using indices.
  -/
  | introMVar (i : Nat) (type : Expr)
  /--
  Use instance synthesization to compute the `i`th parameter.
  `type` represents the type of what to put in `i`, with parameters abstracted
  and level parameters described using indices.
  If `necessary` is false, then it is also filled out by a right-hand side parameter.
  -/
  | synth (necessary : Bool) (i : Nat) (type : Expr)
  /--
  Insert a particular exact value.
  `expr` represents the expression to put in `i`, with parameters abstracted
  and level parameters described using indices.
  -/
  | exact (i : Nat) (expr : Expr)
  /--
  Provide a proof that `rel lhs rhs` as an `i`th parameter.
  `lhs` represents the index of the parameter for the left-hand side and `rhs`
  the index for the right-hand side.
  `rel` represents the relation to use, with parameters abstracted and level
  parameters described using indices.
  -/
  | rel (i : Nat) (lhs rhs : Nat) (rel : Expr)
  deriving Inhabited, Repr

structure NewSimpleCongr where
  /--
  Arity of the function.
  -/
  funArity : Nat
  /--
  The amount of parameters for the proof declaration.
  -/
  proofArity : Nat
  /--
  The indices of the level parameters to use for the proof declaration,
  indexing into the application function levels.
  -/
  lparamsPerm : List Nat
  /-- How to treat the relation arguments. -/
  relArgsIterate : Array CongrAssignmentType
  /-- How to treat the left-hand side arguments. -/
  lhsArgsIterate : Array CongrAssignmentType
  /-- How to treat the right-hand side arguments. -/
  rhsArgsIterate : Array CongrAssignmentType
  /-- Everything that needs to be done until all `.rel` actions are done. -/
  preActions : Array CongrActionType
  /--
  Everything to do after all `.rel` actions are done. These are usually less
  important proof assignments using `.synth` or `.exact`.
  Shouldn't contains `.rel` actions.
  -/
  postActions : Array CongrActionType
  deriving Inhabited, Repr

inductive Procedure where
  | expensiveProcedure (hypothesesPos : Array Nat)
  | simpleProcedure (thm : SimpleCCongrProcedure)
  | newSimpleProcedure (thm : NewSimpleCongr)
deriving Inhabited, Repr

structure CCongrTheorem where
  rel : Name -- name of the relation
  funName : Name
  thmName : Name
  priority : Nat
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

  rel.withApp fun relFn relArgs => lhs.withApp fun lhsFn lhsArgs => rhs.withApp fun rhsFn rhsArgs => do
    let some relName := relFn.constName? | throwError "invalid 'ccongr' theorem, relation application expected{indentExpr type}"
    unless lhsFn.isConst && rhsFn.isConst && lhsFn.constName! == rhsFn.constName! && lhsArgs.size == rhsArgs.size do
      throwError "invalid 'ccongr' theorem, left/right-hand sides must be applications of the same function{indentExpr type}"
    let (lperm, lfun) ← deriveLevelParamPerm lhsFn c.levelParams
    let mut params := #[]
    let mut mvarIdToPurpose : MVarIdMap ParameterFillOutProcedure := ∅
    let mut i := 0
    for x in relArgs do
      unless x.isMVar do
        continue
      mvarIdToPurpose := mvarIdToPurpose.insert x.mvarId! (.relParam i)
      i := i + 1
    i := 0
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
        let rel' := (rel.abstract (relArgs ++ lhsArgs)).instantiateLevelParamsCore lfun
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

inductive CongrAssignmentMode where
  | rel | lhs | rhs
  deriving Inhabited, Repr

inductive MVarAssignState where
  | none | rel | lhs | rhs
  deriving Inhabited, Repr

def mkNewSimpleCongrForDecl (decl : Name) (priority : Nat) : MetaM CCongrTheorem := withReducible do
  let c ← getConstVal decl
  let type := c.type
  let (xs, bis, t) ← forallMetaTelescopeReducing type
  let mkApp2 rel lhs rhs := t |
    throwError "invalid simple ccongr, not a relation application: {t}"
  rel.withApp fun relFn relArgs =>
  lhs.withApp fun lhsFn lhsArgs =>
  rhs.withApp fun rhsFn rhsArgs => do
    unless relFn.isConst do
      throwError "invalid simple ccongr, relation is not a constant application: {rel}"
    let (lperm, lfun) ← deriveLevelParamPerm lhsFn c.levelParams
    let relName := relFn.constName!
    if ((← getEnv).findAsync? (.str relName "trans")).isNone then
      throwError "invalid simple ccongr, relation {relName} doesn't have a `trans` lemma: {rel}"
    unless lhsFn.isConst && rhsFn.isConst && lhsFn.constName! == rhsFn.constName! do
      throwError "invalid simple ccongr, left and right-hand sides aren't applications of the same function: {t}"
    unless lhsArgs.size == rhsArgs.size do
      throwError "invalid simple ccongr, left and right-hand sides have a different amount of parameters: {t}"
    unless lhsFn.constLevels! == rhsFn.constLevels! do
      throwError "invalid simple ccongr, left and right-hand sides have different universe levels: {t}"
    let mut map : MVarIdMap (Nat × MVarAssignState) := ∅
    let mut i := 0
    for x in xs do
      map := map.insert x.mvarId! (i, .none)
      i := i + 1
    let (relArgTypes, map') ← collectAssignmentTypes .rel relArgs map
    let (lhsArgTypes, map') ← collectAssignmentTypes .lhs lhsArgs map'
    let (rhsArgTypes, map') ← collectAssignmentTypes .rhs rhsArgs map'
    map := map'
    let mut actions : Array CongrActionType := #[]
    let mut postActions : Array CongrActionType := #[]
    let mut relDependents : MVarIdSet := ∅
    for x in xs, bi in bis do
      if bi.isInstImplicit || bi.isImplicit then
        continue
      let mvar := x.mvarId!
      let info := map.find! mvar
      let type ← mvar.getType'
      unless info.2 matches .none do
        continue
      if let some (_, _, _) ← CnSimp.checkIsRel type then
        for mm in (← mvar.getMVarDependencies) do
          relDependents := relDependents.insert mm
    for x in xs, bi in bis do
      let mvar := x.mvarId!
      let info := map.find! mvar
      let type ← mvar.getType'
      if bi.isInstImplicit then
        if info.2 matches .rel | .lhs then
          continue
        let type := abstractVars xs lfun type
        let stat := .synth (info.2 matches .none) info.1 type
        if relDependents.contains mvar || info.2 matches .none then
          actions := actions.push stat
        else
          postActions := postActions.push stat
      else if bi.isImplicit then
        unless info.2 matches .none do
          continue
        let type := abstractVars xs lfun type
        let stat := .introMVar info.1 type
        if relDependents.contains mvar then
          actions := actions.push stat
        else
          postActions := postActions.push stat
      else
        unless info.2 matches .none do
          continue
        if let some (rel, lhs, rhs) ← CnSimp.checkIsRel type then
          if lhs.isMVar && rhs.isMVar then
            let lInfo := map.find! lhs.mvarId!
            let rInfo := map.find! rhs.mvarId!
            let rel := abstractVars xs lfun rel
            actions := actions.push (.rel info.1 lInfo.1 rInfo.1 rel)
            continue
          else
            logInfo m!"not rel correct: {type}"
        if type.isOptParam then
          let value := abstractVars xs lfun type.appArg!
          actions := actions.push (.exact info.1 value)
        else
          logInfo m!"not rel: {type}"
    return {
      thmName := decl,
      rel := relName
      funName := lhsFn.constName!
      priority := priority
      procedure := .newSimpleProcedure {
        funArity := lhsArgs.size
        proofArity := xs.size
        lparamsPerm := lperm
        relArgsIterate := relArgTypes
        lhsArgsIterate := lhsArgTypes
        rhsArgsIterate := rhsArgTypes
        preActions := actions
        postActions := postActions
      }
    }
where
  abstractVars (mvars : Array Expr) (lfun : Name → Option Level) (e : Expr) : Expr :=
    (e.abstract mvars.reverse).instantiateLevelParamsCore lfun
  collectAssignmentTypes (mode : CongrAssignmentMode) (args : Array Expr)
      (mvarMap : MVarIdMap (Nat × MVarAssignState)) :
      MetaM (Array CongrAssignmentType × MVarIdMap (Nat × MVarAssignState)) := do
    let mut mvarMap := mvarMap
    let mut types := #[]
    for arg in args do
      unless arg.isMVar do
        if mode matches .lhs | .rhs then
          throwError "invalid simple ccongr, left or right-hand side has concrete argument: {arg}"
        types := types.push .ignore -- resolved through typing (...hopefully?)
        continue
      let mvar := arg.mvarId!
      let info := mvarMap.find! mvar
      if info.2 matches .none then
        types := types.push (.assign info.1)
        let state := match mode with
        | .rel => .rel
        | .lhs => .lhs
        | .rhs => .rhs
        mvarMap := mvarMap.insert mvar (info.1, state)
      else if mode matches .rhs then
        types := types.push (.take info.1)
      else
        types := types.push .ignore -- resolved through typing (...hopefully?)
    return (types, mvarMap)

def addCCongrTheorem (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  try
    let lemma ← mkNewSimpleCongrForDecl declName prio
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

def traverseNewTypes (e : Expr) (rules : Array CongrAssignmentType) (state : Array Expr) : MetaM (Array Expr) :=
  go e state rules.size (Nat.le_refl _)
where
  go (e : Expr) (state : Array Expr) (i : Nat) (hi : i ≤ rules.size) : MetaM (Array Expr) :=
    match h : i with
    | 0 => pure state
    | k + 1 =>
      match e with
      | .mdata _ e => go e state i (h ▸ hi)
      | .app f a =>
        match rules[k]'hi with
        | .assign n => go f (state.set! n a) k (Nat.le_of_lt hi)
        | .take n => do
          go f (state.set! n a) k (Nat.le_of_lt hi) -- maybe check
        | .ignore => go f state k (Nat.le_of_lt hi)
      | _ => pure state

def constructFromTypes (fn : Expr) (rules : Array CongrAssignmentType) (state : Array Expr) : MetaM Expr :=
  go fn 0
where
  go (e : Expr) (i : Nat) : MetaM Expr :=
    if h : i < rules.size then
      match rules[i]'h with
      | .assign n | .take n => go (.app e state[n]!) (i + 1)
      | .ignore =>
        throwError "invalid congruence, did not expect .ignore on rhs"
    else
      pure e
  termination_by rules.size - i

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
  let keys ← DiscrTree.mkPath lhs
  return {
    post := post
    proof := e
    origin := origin
    rfl := false
    keys := keys
  }

def mkSimpTheoremConst (c : Name) (post : Bool := true) (inv : Bool := false) : MetaM (List SimpTheorem) := withReducible do
  let some val := (← getEnv).findConstVal? c | throwError "unknown constant '{c}'"
  let type := val.type
  if inv then
    let proof : Expr := .const c (val.levelParams.map Level.param)
    let origin := .decl c post inv
    (← preprocess proof type true).mapM (fun (proof, type) => do
      let (_, _, e) ← forallMetaTelescopeReducing type
      let mkApp2 _ lhs _ := e | throwError "must be relation blah"
      mkSimpTheoremCore proof lhs origin post)
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
