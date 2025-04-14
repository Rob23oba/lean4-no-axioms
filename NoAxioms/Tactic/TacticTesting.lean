import Lean.Elab.Tactic
import NoAxioms.Tactic.CongrSimpExt

open Lean Meta

namespace CnSimp

open CCongr

deriving instance Repr for Simp.Result

structure State where
  cache : Std.HashMap (Expr × Expr) (Option Meta.Simp.Result) := ∅

abbrev CnSimpM := StateRefT State $ ReaderT SimpTheorems MetaM

mutual

partial def forallCongr (lhs : Expr) : CnSimpM (Option Meta.Simp.Result) := do
  let .forallE nm t b bi := lhs | return none
  let mut result := none
  let lvl ← getLevel t
  if lvl.isAlwaysZero then
    result ← cnsimp (mkConst ``Iff) t
  forallBoundedTelescope lhs (some 1) fun fvars inner => do
    unless ← isProp inner do
      return none
    let result2 ← cnsimp (mkConst ``Iff) inner
    match result, result2 with
    | none, none => return none
    | some { expr := t', proof? := pt, .. }, none =>
      let repl := match pt with
        | none => mkApp2 (.const ``id [0]) t' (.bvar 0)
        | some pt => mkApp4 (.const ``Iff.mpr []) t t' pt (.bvar 0)
      let newExpr : Expr := .forallE nm t' (b.instantiate1 repl) bi
      let proof : Expr := match pt with
        | none => .app (.const ``Iff.rfl []) newExpr
        | some pt =>
          mkApp4 (.const ``forall_prop_dom_congr []) t t' (.lam nm t b bi) pt
      return some { expr := newExpr, proof? := some proof }
    | none, some { expr := b', proof? := pb, .. } =>
      let b'' := b'.abstract fvars
      let newExpr : Expr := .forallE nm t b'' bi
      let proof : Expr ← match pb with
        | none => pure (.app (.const ``Iff.rfl []) newExpr)
        | some pb =>
          pure (mkApp4 (.const ``forall_congr' [lvl]) t (.lam nm t b bi) (.lam nm t b'' bi) (← mkLambdaFVars fvars pb))
      return some { expr := newExpr, proof? := some proof }
    | some { expr := t', proof? := pt, .. }, some { expr := b', proof? := pb, .. } =>
      let b'' := b'.abstract fvars
      let repl := match pt with
        | none => mkApp2 (.const ``id [0]) t' (.bvar 0)
        | some pt => mkApp4 (.const ``Iff.mpr []) t t' pt (.bvar 0)
      let b''' := b''.instantiate1 repl
      let newExpr : Expr := .forallE nm t' b''' bi
      let proof : Expr ← match pt, pb with
        | none, none => pure (.app (.const ``Iff.rfl []) newExpr)
        | none, some pb =>
          pure (mkApp4 (.const ``forall_congr' [lvl]) t (.lam nm t b bi) (.lam nm t b'' bi) (← mkLambdaFVars fvars pb))
        | some pt, none =>
          pure (mkApp4 (.const ``forall_prop_dom_congr []) t t' (.lam nm t b bi) pt)
        | some pt, some pb =>
          pure (mkApp6 (.const ``forall_prop_congr []) t t' (.lam nm t b bi) (.lam nm t b'' bi) pt (← mkLambdaFVars fvars pb))
      return some { expr := newExpr, proof? := some proof }

partial def rewriteOne (rel : Expr) (lhs : Expr) (pre : Bool) : CnSimpM Meta.Simp.Step := do
  trace[Meta.Tactic.simp.rewrite] m!"try to rewrite: {rel} {lhs} {pre}"
  let thms ← readThe SimpTheorems
  let mut lhs := lhs
  let matchList ← (if pre then thms.pre else thms.post).getMatch lhs
  for m in matchList do
    let proof ← m.getValue
    let (xs, _, type) ← forallMetaTelescopeReducing (← inferType proof)
    let rhs ← mkFreshExprMVar none
    let e := mkApp2 rel lhs rhs
    unless ← isDefEq type e do
      trace[Meta.Tactic.simp.rewrite] m!"failed to unify {type} and {e}"
      continue
    -- rewriting
    let mut newParams : Array Expr := #[]
    let mut failed := false
    for m in xs do
      if (← m.mvarId!.getKind) matches .synthetic then
        try
          m.mvarId!.assign (← synthInstance (← m.mvarId!.getType))
        catch e =>
          trace[Meta.Tactic.simp.rewrite] m!"rewrite failed, {e.toMessageData}"
          failed := true
          break
      let m ← instantiateMVars m
      if m.hasExprMVar then
        trace[Meta.Tactic.simp.rewrite] m!"rewrite failed, proof has mvar{indentExpr m}"
        failed := true
        break
      newParams := newParams.push m
    if failed then
      continue
    let rhs ← instantiateMVars rhs
    trace[Meta.Tactic.simp.rewrite] m!"rewrite: {m.proof} to {rhs}"
    return .visit {
      expr := rhs
      proof? := mkAppN proof newParams
    }
  return .continue

partial def condenseSteps (steps : Array Expr) (rel expr : Expr) : CnSimpM Simp.Result := do
  if steps.isEmpty then
    return { expr := expr }
  let relName := rel.getAppFn'.constName!
  let mut proof := steps.back!
  let mut steps := steps.pop
  while !steps.isEmpty do
    let proof' := steps.back!
    proof ← mkAppM (.str relName "trans") #[proof', proof]
    steps := steps.pop
  return { expr := expr, proof? := proof }

partial def rewriting (rel : Expr) (lhs : Expr) (pre : Bool) : CnSimpM Simp.Step := do
  let relName := rel.getAppFn'.constName!
  let mut proofSteps : Array Expr := #[]
  let mut lhs := lhs
  let mut done := false
  repeat
    let step ← rewriteOne rel lhs pre
    match step with
    | .visit { expr := expr, proof? := proof, cache := _ } =>
      let proof ← match proof with
        | some p => pure p
        | none => mkAppM (.str relName "refl") #[expr]
      proofSteps := proofSteps.push proof
      lhs := expr
      continue
    | .continue none =>
      break
    | .continue (some { expr := expr, proof? := proof, cache := _ }) =>
      let proof ← match proof with
        | some p => pure p
        | none => mkAppM (.str relName "refl") #[expr]
      proofSteps := proofSteps.push proof
      lhs := expr
      continue
    | .done { expr := expr, proof? := proof, cache := _ } =>
      let proof ← match proof with
        | some p => pure p
        | none => mkAppM (.str relName "refl") #[expr]
      proofSteps := proofSteps.push proof
      lhs := expr
      done := true
      break
  if proofSteps.isEmpty then
    return .continue
  let result ← condenseSteps proofSteps rel lhs
  if done then
    return .done result
  return .continue (some result)

partial def trySimpleCongr (rel lhs : Expr) (c : CCongrTheorem) (p : SimpleCCongrProcedure) : CnSimpM (Option Meta.Simp.Result) := withReducible do
  let lhsArgs := lhs.getAppArgs'
  if lhsArgs.size != p.arity then
    --trace[Meta.Tactic.simp.congr] m!"tried applying {c.thmName} to {lhs}, arity mismatch: {lhsArgs.size} vs {p.arity}"
    return none
  let relArgs := rel.getAppArgs'
  let args := relArgs ++ lhsArgs
  -- first go through parameters for rewrites
  let levels := lhs.getAppFn'.constLevels!
  let mut relSteps := #[]
  let mut madeProgress := false
  --trace[Meta.Tactic.simp.congr] m!"have params {reprPrec p.params 0}"
  for param in p.params do
    if let .rel rel' n := param then
      let newRel := (rel'.instantiateRev args).instantiateLevelParamsCore
        (fun n => match n with | .num _ n => levels[n]! | _ => none)
      let newLhs := lhsArgs[n]!
      trace[Meta.Tactic.simp.congr] m!"relation param {newRel} {newLhs}"
      let step ← cnsimp newRel newLhs
      madeProgress := madeProgress || step.isSome
      relSteps := relSteps.push step
  unless madeProgress do
    trace[Meta.Tactic.simp.congr] m!"no progress for congruence with {c.thmName} in {lhs} {rel}"
    return none
  -- now construct the proof
  let lparams := p.lparamPerm.map (levels[·]!)
  let mut rhsArgs := Array.replicate p.arity default
  let mut irel := 0
  for param in p.params do
    match param with
    | .fixed i =>
      rhsArgs := rhsArgs.set! i lhsArgs[i]!
    | .rel _ i =>
      let step := relSteps[irel]!
      irel := irel + 1
      match step with
      | none => rhsArgs := rhsArgs.set! i lhsArgs[i]!
      | some { expr := rhs, proof? := _, cache := _ } =>
        rhsArgs := rhsArgs.set! i rhs
    | _ => pure ()
  let mut proofParams : Array Expr := Array.emptyWithCapacity p.params.size
  irel := 0
  let mut iparam := 0
  for param in p.params do
    match param with
    | .relParam i =>
      proofParams := proofParams.push relArgs[i]!
    | .preParam i | .fixed i =>
      proofParams := proofParams.push lhsArgs[i]!
    | .postParam i .none =>
      proofParams := proofParams.push rhsArgs[i]!
    | .postParam i (.synth dischType) =>
      let dischType := (dischType.instantiateRev proofParams).instantiateLevelParamsCore
        (fun n => match n with | .num _ n => levels[n]! | _ => none)
      trace[Meta.Tactic.simp.discharge] m!"try to discharge {dischType} for {c.thmName}"
      try
        let val ← synthInstance dischType
        rhsArgs := rhsArgs.setIfInBounds i val
        proofParams := proofParams.push val
      catch _ =>
        return none
    | .postParam i (.exact disch) =>
      let disch := (disch.instantiateRev proofParams).instantiateLevelParamsCore
        (fun n => match n with | .num _ n => levels[n]! | _ => none)
      rhsArgs := rhsArgs.setIfInBounds i disch
      proofParams := proofParams.push disch
    | .rel rel' i =>
      let step := relSteps[irel]!
      irel := irel + 1
      let relName := rel'.getAppFn'.constName!
      match step with
      | none => proofParams := proofParams.push (← mkAppM (.str relName "refl") #[lhsArgs[i]!])
      | some { expr := rhs, proof? := proof?, cache := _ } =>
        proofParams := proofParams.push (← proof?.getDM (mkAppM (.str relName "refl") #[rhs]))
    iparam := iparam + 1
  let rhs := mkAppN lhs.getAppFn' rhsArgs
  let proof : Expr := .const c.thmName lparams
  let proof := mkAppN proof proofParams
  return some { expr := rhs, proof? := proof }

partial def tryCongr (rel lhs : Expr) (c : CCongrTheorem) (pos : Array Nat) : CnSimpM (Option Meta.Simp.Result) := withReducible do
  --trace[Meta.Tactic.simp.congr] m!"try congruence {rel} {lhs} {c.thmName}"
  let some const := (← getEnv).findConstVal? c.thmName | return none
  let levels ← mkFreshLevelMVars const.levelParams.length
  let type := const.type.instantiateLevelParams const.levelParams levels
  let (xs, _, type) ← forallMetaTelescopeReducing type
  let rhs ← mkFreshExprMVar none
  let e := mkApp2 rel lhs rhs
  unless ← isDefEq e type do
    trace[Meta.Tactic.simp.congr] m!"congruence failed: failed to unify {e} and {type}"
    return none
  let mut madeProgress := false
  for i in pos do
    let goal := xs[i]!.mvarId!
    if ← goal.isAssigned then
      continue
    let type ← goal.getType'
    let expr : Option (Expr × Bool) ← forallTelescope type fun fvars newType => do
      let mkApp2 rel' lhs' rhs' := newType | return none
      let relName' := rel'.getAppFn'.constName!
      let step ← cnsimp rel' lhs'
      let progress := step.isSome
      let thing ←
        match step with
        | none => pure (lhs', ← mkAppM (.str relName' "refl") #[lhs'])
        | some { expr := rhs, proof? := some proof, cache := _ } =>
          pure (rhs, proof)
        | some { expr := rhs, proof? := none, cache := _ } =>
          pure (rhs, ← mkAppM (.str relName' "refl") #[rhs])
      let ((rhs : Expr), proof) := thing
      unless ← isDefEq rhs' rhs do
        trace[Meta.Tactic.simp.congr] m!"inner congruence failed: failed to unify {rhs} and {rhs'}"
        return none
      let proof ← proof.abstractM fvars
      let proof ← fvars.foldrM (fun fvar proof =>
        return (.lam `x (← fvar.fvarId!.getType) proof .default)) proof
      return some (proof, progress)
    let some (expr, progress) := expr | return none
    goal.assign expr
    madeProgress := madeProgress || progress
  unless madeProgress do
    return none
  let proof : Expr := .const c.thmName levels
  let proof := mkAppN proof xs
  let rhs ← instantiateMVars rhs
  return some { expr := rhs, proof? := proof }

partial def doCongr (rel lhs : Expr) : CnSimpM (Option Meta.Simp.Result) := do
  --trace[Meta.Tactic.simp.congr] m!"visiting subexpressions for {rel} and {lhs}"
  let lhs := lhs.consumeMData
  if lhs.isForall ∧ rel.isConstOf ``Iff then
    return ← forallCongr lhs
  let app := lhs.getAppFn'
  unless app.isConst do
    --trace[Meta.Tactic.simp.congr] m!"application not supported {rel} and {app}"
    return none -- not supported currently
  let relName := rel.getAppFn'.constName!
  let state := ccongrExtension.getState (← getEnv)
  let some congr := state.lemmas.find? { rel := relName, decl := app.constName! } |
    --trace[Meta.Tactic.simp.congr] m!"no congruence found for {rel} and {app}"
    return none
  for c in congr do
    let step ← match c.procedure with
    | .simpleProcedure p => trySimpleCongr rel lhs c p
    | .expensiveProcedure p => tryCongr rel lhs c p
    if step.isSome then
      return step
  --trace[Meta.Tactic.simp.congr] m!"no progress made for {rel} and {lhs}"
  return none

-- creates a proof of `rel lhs rhs` where `rhs` is also returned.
partial def cnsimp (rel : Expr) (lhs : Expr) : CnSimpM (Option Meta.Simp.Result) := withReducible do
  if let some result := (← getThe State).cache[(rel, lhs)]? then
    trace[Meta.Tactic.simp] m!"cached {reprPrec result 0} for {rel} {lhs}"
    return result
  let mut proofSteps : Array Expr := #[]
  let mut madeProgress := false
  let origLhs := lhs
  let mut lhs := lhs
  repeat
    let rwStep ← rewriting rel lhs (pre := true)
    match rwStep with
    | .done { expr := expr, proof? := proof?, cache := _ } =>
      lhs := expr
      if let some proof := proof? then
        proofSteps := proofSteps.push proof
      madeProgress := true
      break
    | .visit _ => unreachable!
    | .continue res =>
    match res with
    | none => pure ()
    | some { expr := expr, proof? := proof?, cache := _ } =>
      lhs := expr
      if let some proof := proof? then
        proofSteps := proofSteps.push proof
      madeProgress := true
    let cng ← doCongr rel lhs
    match cng with
    | none => pure ()
    | some { expr := expr, proof? := proof?, cache := _ } =>
      lhs := expr
      if let some proof := proof? then
        proofSteps := proofSteps.push proof
      madeProgress := true
    let rwStep ← rewriting rel lhs (pre := false)
    match rwStep with
    | .done { expr := expr, proof? := proof?, cache := _ } =>
      lhs := expr
      if let some proof := proof? then
        proofSteps := proofSteps.push proof
      madeProgress := true
      break
    | .visit _ => unreachable!
    | .continue (some { expr := expr, proof? := proof?, cache := _ }) =>
      let prev := lhs
      lhs := expr
      if let some proof := proof? then
        proofSteps := proofSteps.push proof
      madeProgress := true
      if expr != prev then
        continue
    | _ => break
  let result ← if madeProgress then pure <| some (← condenseSteps proofSteps rel lhs) else pure none
  modifyThe State fun state => { state with cache := state.cache.insert (rel, origLhs) result }
  return result

end

end CnSimp

open Elab Tactic

open Parser Tactic

syntax (name := cnsimpTac) "cnsimp" optConfig (discharger)? (&" only")?
    (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

def CnSimp.mkSimpTheoremCoreOther (origin : Origin) (e : Expr) (levelParams : Array Name) (proof : Expr) (post : Bool) (prio : Nat) (noIndexAtArgs : Bool) : MetaM SimpTheorem := do
  assert! origin != .fvar ⟨.anonymous⟩
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    let type ← whnfR type
    let keys ←
      match type with
      | mkApp2 _ lhs _ => DiscrTree.mkPath lhs noIndexAtArgs
      | _ => throwError "unexpected kind of 'cnsimp' theorem{indentExpr type}"
    trace[Meta.Tactic.simp] m!"keys: {keys} for type {type}"
    return { origin, keys, post, levelParams, proof, priority := prio, rfl := (← isRflProof proof) }

def CnSimp.addLocalSimpLemma (thms : SimpTheorems) (e : Expr) (origin : Origin) (post : Bool := true) (inv : Bool := false) : MetaM SimpTheorems := withReducible do
  let type ← inferType e
  unless (← isProp type) do
    throwError "invalid 'cnsimp', proposition expected{indentExpr type}"
  let vers ← preprocess e type inv
  let mut thms := thms
  for (proof, _) in vers do
    let thm ← mkSimpTheoremCoreOther origin proof #[] proof post (eval_prio default) true
    if post then
      return { thms with post := thms.post.insertCore thm.keys thm }
    else
      return { thms with pre := thms.pre.insertCore thm.keys thm }
  return thms

def CnSimp.addCnSimpLemmas (stx : Syntax) (thms : SimpTheorems) : TacticM SimpTheorems := do
  if stx.isNone then
    return thms
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    let go := withMainContext do
      let mut thms      := thms
      let mut starArg   := false
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]
          match (← resolveSimpIdTheorem? ⟨term⟩) with
          | some e@(.const _ _) =>
            for thm in ← CnSimp.mkSimpTheoremConst e.constName! post inv do
              thms := addSimpTheoremEntry thms thm
          | _ =>
            let name ← mkFreshId
            let term ← elabTerm term none
            thms ← addLocalSimpLemma thms term (.stx name arg) post inv
        else
          throwUnsupportedSyntax
      return thms
    go
where
  resolveSimpIdTheorem? (simpArgTerm : Term) : TacticM (Option Expr) := do
    match simpArgTerm with
    | `($id:ident) =>
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          return some e
        return none
      catch _ =>
        return none
    | _ =>
      if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
        return some e
      else
        return none

def applyCnSimpIffResult (goalType : Expr) (res : Simp.Result) : TacticM Unit := do
  let goal ← getMainGoal
  let newGoal ← mkFreshExprMVar res.expr
  let step := match res.proof? with
    | none => mkApp2 (.const ``id [0]) res.expr newGoal
    | some val => mkApp4 (.const ``Iff.mpr []) goalType res.expr val newGoal
  goal.assign step
  if res.expr.isTrue then
    newGoal.mvarId!.assign (.const ``trivial [])
  else
    replaceMainGoal [newGoal.mvarId!]

def applyCnSimpIffResultLocal (goalType : Expr) (fvar : FVarId) (res : Simp.Result) : TacticM Unit := do
  let goal ← getMainGoal
  let step := match res.proof? with
    | none => mkApp2 (.const ``id [0]) res.expr (.fvar fvar)
    | some val => mkApp4 (.const ``Iff.mp []) goalType res.expr val (.fvar fvar)
  let res ← goal.replace fvar step res.expr
  replaceMainGoal [res.mvarId]

@[tactic cnsimpTac]
def elabCnSimp : Tactic := fun stx => do
  --let cfg := stx[1]
  let only := stx[3]
  let mut theorems : SimpTheorems := {}
  if only.isNone then
    theorems ← cnsimpExt.getTheorems
  withMainContext <| withLocation (expandOptLocation stx[5])
    (atLocal := fun f => do
      let theorems ← CnSimp.addCnSimpLemmas stx[4] theorems
      let goalType ← instantiateMVars (← f.getType)
      let step ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run' {} theorems
      let some step := step | throwError "cnsimp made no progress"
      applyCnSimpIffResultLocal goalType f step)
    (atTarget := do
      let theorems ← CnSimp.addCnSimpLemmas stx[4] theorems
      let goal ← getMainGoal
      let goalType ← instantiateMVars (← goal.getType)
      let step ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run' {} theorems
      let some step := step | throwError "cnsimp made no progress"
      applyCnSimpIffResult goalType step)
    (failed := fun _ => throwError "cnsimp made no progress")
