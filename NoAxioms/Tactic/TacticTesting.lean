import Lean.Elab.Tactic
import NoAxioms.Tactic.CongrSimpExt

open Lean Meta

namespace CnSimp

open CCongr

deriving instance Repr for Simp.Result

structure Config where
  singlePass : Bool := false

structure Context where
  theorems : SimpTheorems
  config : Config

structure State where
  cache : Std.HashMap (Expr × Expr) Meta.Simp.Result := ∅
  usedSimps : Simp.UsedSimps := {}

abbrev CnSimpM := StateRefT State $ ReaderT Context MetaM

def registerUsedSimp (x : Origin) : CnSimpM Unit := do
  modifyThe State fun a => { a with usedSimps := a.usedSimps.insert x }

def appendToFnName (e : Expr) (s : String) : Expr :=
  match e with
  | .app a b => e.updateApp! (appendToFnName a s) b
  | .const nm us => .const (.str nm s) us
  | e => e

def reflApp (rel a : Expr) : Expr :=
  mkApp (appendToFnName rel "refl") a

def symmApp (rel a b h : Expr) : Expr :=
  mkApp3 (appendToFnName rel "symm") a b h

def transApp (rel a b c h h' : Expr) : Expr :=
  mkApp5 (appendToFnName rel "trans") a b c h h'

def mkTrans (rel expr : Expr) (res res' : Simp.Result) : Simp.Result :=
  match res, res' with
  | { proof? := none, .. }, step => step
  | { proof? := some prf, .. }, { expr, proof? := none, .. } => { expr, proof? := some prf }
  | { expr := expr1, proof? := some prf, .. }, { expr := expr2, proof? := some prf', .. } =>
    { expr := expr2, proof? := some (transApp rel expr expr1 expr2 prf prf') }

mutual

partial def forallCongr (lhs : Expr) : CnSimpM Simp.Result := do
  let .forallE nm t b bi := lhs | return { expr := lhs }
  let mut lhs := lhs
  let mut result : Simp.Result := { expr := t }
  let lvl ← getLevel t
  if lvl.isAlwaysZero then
    result ← cnsimp (mkConst ``Iff) t
  withLocalDecl nm bi t fun var => do
    let inner := b.instantiate1 var
    unless ← isProp inner do
      return { expr := lhs }
    let result2 ← cnsimp (mkConst ``Iff) inner
    match result, result2 with
    | { expr := t', proof? := pt, .. }, { expr := b', proof? := pb, .. } =>
      let b'' := b'.abstract #[var]
      let repl := match pt with
        | none => mkApp2 (.const ``id [0]) t' (.bvar 0)
        | some pt => mkApp4 (.const ``Iff.mpr []) t t' pt (.bvar 0)
      let b''' := if t' != t then b''.instantiate1 repl else b''
      let newExpr : Expr := .forallE nm t' b''' bi
      let proof : Expr ← match pt, pb with
        | none, none => pure (.app (.const ``Iff.rfl []) newExpr)
        | none, some pb =>
          pure (mkApp4 (.const ``forall_congr' [lvl]) t (.lam nm t b bi) (.lam nm t b'' bi) (← mkLambdaFVars #[var] pb))
        | some pt, none =>
          pure (mkApp4 (.const ``forall_prop_dom_congr []) t t' (.lam nm t b bi) pt)
        | some pt, some pb =>
          pure (mkApp6 (.const ``forall_prop_congr []) t t' (.lam nm t b bi) (.lam nm t b'' bi) pt (← mkLambdaFVars #[var] pb))
      return { expr := newExpr, proof? := some proof }

partial def rewriteOne (rel : Expr) (lhs : Expr) (pre : Bool) : CnSimpM Simp.Step := do
  trace[Meta.Tactic.simp.rewrite] m!"try to rewrite: {rel} {lhs} {pre}"
  let ctx ← readThe Context
  let thms := ctx.theorems
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
    registerUsedSimp m.origin
    return .visit {
      expr := rhs
      proof? := mkAppN proof newParams
    }
  return .continue

partial def rewriting (rel : Expr) (lhs : Expr) (pre : Bool) : CnSimpM Simp.Step := do
  let origLhs := lhs
  let mut res : Simp.Result := { expr := lhs }
  let mut lhs := lhs
  let mut done := false
  repeat
    let step ← rewriteOne rel lhs pre
    match step with
    | .visit res' =>
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      break
    | .continue none =>
      return .continue
    | .continue (some res') =>
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      break
    | .done res' =>
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      done := true
      break
  if done then
    return .done res
  return .continue (some res)

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
  let mut refl := true
  --trace[Meta.Tactic.simp.congr] m!"have params {reprPrec p.params 0}"
  for param in p.params do
    if let .rel rel' n := param then
      let newRel := (rel'.instantiateRev args).instantiateLevelParamsCore
        (fun n => match n with | .num _ n => levels[n]! | _ => none)
      let newLhs := lhsArgs[n]!
      trace[Meta.Tactic.simp.congr] m!"relation param {newRel} {newLhs}"
      let step ← cnsimp newRel newLhs
      refl := refl && step.proof?.isNone
      madeProgress := madeProgress || step.expr != newLhs
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
      rhsArgs := rhsArgs.set! i step.expr
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
    | .rel rel' _ =>
      let step := relSteps[irel]!
      irel := irel + 1
      proofParams := proofParams.push (step.proof?.getD (reflApp rel' step.expr))
    iparam := iparam + 1
  let rhs := mkAppN lhs.getAppFn' rhsArgs
  let proof : Expr := .const c.thmName lparams
  let proof := mkAppN proof proofParams
  return some { expr := rhs, proof? := if refl then proof else none }

partial def tryNewSimpleCongr (rel lhs : Expr) (c : CCongrTheorem) (p : NewSimpleCongr) : CnSimpM (Option Meta.Simp.Result) := withReducible do
  let lhsArgs := lhs.getAppArgs'
  if lhsArgs.size != p.funArity then
    return none
  let state : Array Expr := Array.replicate p.proofArity default
  let state ← traverseNewTypes rel p.relArgsIterate state
  let state ← traverseNewTypes lhs p.lhsArgsIterate state
  trace[Meta.Tactic.simp.congr] m!"state: {state}"
  let levels := lhs.getAppFn'.constLevels!
  let some (refl, state) ← doActions levels false state p.preActions | return none
  let some (_, state) ← doActions levels true state p.postActions | return none
  let rhs ← constructFromTypes lhs.getAppFn' p.rhsArgsIterate state
  if refl then
    return some { expr := rhs }
  let lparams := p.lparamsPerm.map (levels[·]!)
  let proof : Expr := .const c.thmName lparams
  let proof := mkAppN proof state
  return some { expr := rhs, proof? := proof }
where
  doActions (levels : List Level) (madeProgress : Bool) (state : Array Expr) (acts : Array CongrActionType) : CnSimpM (Option (Bool × Array Expr)) := do
    let lfun (n : Name) : Option Level := match n with | .num _ n => levels[n]! | _ => none
    let mut state := state
    let mut refl := true
    let mut madeProgress := madeProgress
    for act in acts do
      match act with
      | .synth _ i type =>
        let type := (type.instantiate state).instantiateLevelParamsCore lfun
        try
          let expr ← synthInstance type
          state := state.set! i expr
        catch _ =>
          trace[Meta.Tactic.simp.congr] m!"discharge for {type} failed"
          return none
      | .exact i value =>
        let value := (value.instantiate state).instantiateLevelParamsCore lfun
        state := state.set! i value
      | .introMVar i type =>
        let type := (type.instantiate state).instantiateLevelParamsCore lfun
        let mvar ← mkFreshExprMVar type
        state := state.set! i mvar
      | .rel i lhs rhs rel =>
        let rel := (rel.instantiate state).instantiateLevelParamsCore lfun
        let step ← cnsimp (← instantiateMVars rel) state[lhs]!
        state := state.set! rhs step.expr
        state := state.set! i (step.proof?.getD (reflApp rel step.expr))
        madeProgress := madeProgress || step.expr != state[lhs]!
        refl := refl && step.proof?.isNone
    if madeProgress then
      return some (refl, state)
    else
      return none

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
      let step ← cnsimp rel' lhs'
      unless ← isDefEq rhs' step.expr do
        trace[Meta.Tactic.simp.congr] m!"inner congruence failed: failed to unify {rhs} and {rhs'}"
        return none
      let proof := step.proof?.getD (reflApp rel' step.expr)
      let proof ← proof.abstractM fvars
      let proof ← fvars.foldrM (fun fvar proof =>
        return (.lam `x (← fvar.fvarId!.getType) proof .default)) proof
      return some (proof, step.expr != lhs')
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
    | .newSimpleProcedure p => tryNewSimpleCongr rel lhs c p
    if step.isSome then
      return step
  --trace[Meta.Tactic.simp.congr] m!"no progress made for {rel} and {lhs}"
  return none

-- creates a proof of `rel lhs rhs` where `rhs` is also returned.
partial def cnsimp (rel : Expr) (lhs : Expr) : CnSimpM Simp.Result := withIncRecDepth <| withReducible do
  if let some result := (← getThe State).cache[(rel, lhs)]? then
    trace[Meta.Tactic.simp] m!"cached {reprPrec result 0} for {rel} {lhs}"
    return result
  withTraceNode `Meta.Tactic.simp (fun _ => return m!"try simp {rel} {lhs}") do
  let mut res : Simp.Result := { expr := lhs }
  let origLhs := lhs
  let mut lhs := lhs
  repeat
    let rwStep ← rewriting rel lhs (pre := true)
    match rwStep with
    | .done res' =>
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      break
    | .visit _ => unreachable!
    | .continue res' =>
    if let some res' := res' then
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
    let cng ← doCongr rel lhs
    if let some res' := cng then
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
    let rwStep ← rewriting rel lhs (pre := false)
    match rwStep with
    | .done res' =>
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      break
    | .visit _ => unreachable!
    | .continue (some res') =>
      let prev := lhs
      res := mkTrans rel origLhs res res'
      lhs := res'.expr
      if res'.expr != prev && !(← read).config.singlePass then
        continue
      break
    | _ => break
  modifyThe State fun state => { state with cache := state.cache.insert (rel, origLhs) res }
  return res

end

end CnSimp

open Elab Tactic

open Parser Tactic

syntax (name := cnsimpTac) "cnsimp " optConfig (discharger)? (&" only")?
    (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

syntax (name := cnsimpTraceTac) "cnsimp? " optConfig (discharger)? (&" only")?
    (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

syntax (name := cnsimpaTac) "cnsimpa " optConfig (discharger)? (&" only")?
    (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (" using " term)? : tactic

syntax (name := cnsimpaTraceTac) "cnsimpa? " optConfig (discharger)? (&" only")?
    (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (" using " term)? : tactic

syntax (name := cnrwTac) "cnrw " optConfig (" [" withoutPosition(rwRule,*,?) "]")? (location)? : tactic

macro_rules
  | `(tactic| cnrw $cfg:configItem* $[[$rules,*]]? $(loc?)?) => do
    let rules := rules.elim #[] (·.getElems)
    let items : TSyntaxArray `tactic ←
      rules.mapM fun stx =>
        match stx with
        | `(rwRule| ← $l:term) => `(tactic| cnsimp%$stx $cfg* +singlePass only [← $l:term] $(loc?)?)
        | `(rwRule| $l:term) => `(tactic| cnsimp%$stx $cfg* +singlePass only [$l:term] $(loc?)?)
        | _ => Macro.throwUnsupported
    let items := items.push (← `(tactic| with_reducible try rfl))
    `(tactic| ($[$items:tactic];*))

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
  let e ← instantiateMVars e
  let mvars ← getMVars e
  let e ← mkLambdaFVars (mvars.map Expr.mvar) e
  let type ← inferType e
  unless (← isProp type) do
    throwError "invalid 'cnsimp', proposition expected{indentExpr type}"
  let vers ← preprocess e type inv
  let mut thms := thms
  for (proof, _) in vers do
    let thm ← mkSimpTheoremCoreOther origin proof #[] proof post (eval_prio default) false
    if post then
      return { thms with post := thms.post.insertCore thm.keys thm }
    else
      return { thms with pre := thms.pre.insertCore thm.keys thm }
  return thms

def CnSimp.addCnSimpLemmas (args : TSyntaxArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]) (thms : SimpTheorems) : TacticM SimpTheorems := do
  withMainContext do
    let mut thms      := thms
    let mut starArg   := false
    for arg in args do
      match arg with
      | `(simpLemma| $x:simpLemma) =>
        let post := !x matches `(simpLemma| ↓$[←]?$_)
        let inv  := x matches `(simpLemma| $[$_]?←$_)
        let term : Term := ⟨x.raw[2]⟩
        match (← resolveSimpIdTheorem? ⟨term⟩) with
        | some e@(.const _ _) =>
          for thm in ← CnSimp.mkSimpTheoremConst e.constName! post inv do
            thms := thms.addSimpTheorem thm
        | _ =>
          let name ← mkFreshId
          let term ← elabTerm term none
          thms ← addLocalSimpLemma thms term (.stx name arg) post inv
      | _ => throwUnsupportedSyntax
    return thms
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

def applyCnSimpIffResult (goal : MVarId) (goalType : Expr) (res : Simp.Result) : MetaM (List MVarId) := do
  let newGoal ← mkFreshExprMVar res.expr
  let step := match res.proof? with
    | none => mkApp2 (.const ``id [0]) res.expr newGoal
    | some val => mkApp4 (.const ``Iff.mpr []) goalType res.expr val newGoal
  goal.assign step
  if res.expr.isTrue then
    newGoal.mvarId!.assign (.const ``trivial [])
    return []
  else
    return [newGoal.mvarId!]

def applyCnSimpIffResultLocal (goal : MVarId) (goalType : Expr) (fvar : FVarId) (res : Simp.Result) : MetaM (List MVarId) := do
  let step := match res.proof? with
    | none => mkApp2 (.const ``id [0]) res.expr (.fvar fvar)
    | some val => mkApp4 (.const ``Iff.mp []) goalType res.expr val (.fvar fvar)
  if res.expr.isFalse then
    goal.assignFalseProof step
    return []
  let res ← goal.replace fvar step res.expr
  return [res.mvarId]

def suggestSimpOnly (state : CnSimp.State) (tk stx : Syntax) : MetaM Unit := do
  let stx := stx.unsetTrailing
  let stx ← mkSimpOnly stx state.usedSimps
  let stx := stx.setArg 0 <|
    match stx.getKind with
    | ``cnsimpTraceTac => .atom .none "cnsimp"
    | ``cnsimpaTraceTac => .atom .none "cnsimpa"
    | _ => stx[0]
  let stx := stx.setKind <|
    match stx.getKind with
    | ``cnsimpTraceTac => ``cnsimpTac
    | ``cnsimpaTraceTac => ``cnsimpaTac
    | k => k
  TryThis.addSuggestion tk (⟨stx⟩ : TSyntax `tactic) (origSpan? := ← getRef)

declare_config_elab elabCnSimpConfig CnSimp.Config

elab_rules : tactic | `(tactic| cnsimp $cfg:optConfig $(_disch?)? $[only%$only]? $[[$lemmas,*]]? $(loc?)?) => do
  let config ← elabCnSimpConfig cfg
  let mut theorems : SimpTheorems := {}
  if only.isNone then
    theorems ← cnsimpExt.getTheorems
  withMainContext <| withLocation (loc?.elim (.targets #[] true) fun s => expandLocation s)
    (atLocal := fun f => do
      let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
      let goalType ← instantiateMVars (← f.getType)
      let step ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run' {} { theorems, config }
      if step.expr == goalType then
        throwError "cnsimp made no progress"
      liftMetaTactic (applyCnSimpIffResultLocal · goalType f step))
    (atTarget := do
      let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
      let goal ← getMainGoal
      let goalType ← instantiateMVars (← goal.getType)
      let step ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run' {} { theorems, config }
      if step.expr == goalType then
        throwError "cnsimp made no progress"
      liftMetaTactic (applyCnSimpIffResult · goalType step))
    (failed := fun _ => throwError "cnsimp made no progress")

@[tactic cnsimpTraceTac]
def evalCnSimpTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| cnsimp?%$tk $cfg:optConfig $(_disch?)? $[only%$only]? $[[$lemmas,*]]? $(loc?)?) => do
    let config ← elabCnSimpConfig cfg
    let mut theorems : SimpTheorems := {}
    if only.isNone then
      theorems ← cnsimpExt.getTheorems
    withMainContext <| withLocation (loc?.elim (.targets #[] true) fun s => expandLocation s)
      (atLocal := fun f => do
        let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
        let goalType ← instantiateMVars (← f.getType)
        let (step, state) ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run {} { theorems, config }
        if step.expr == goalType then
          throwError "cnsimp made no progress"
        suggestSimpOnly state tk stx
        liftMetaTactic (applyCnSimpIffResultLocal · goalType f step))
      (atTarget := do
        let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
        let goal ← getMainGoal
        let goalType ← instantiateMVars (← goal.getType)
        let (step, state) ← (CnSimp.cnsimp (mkConst ``Iff) goalType).run {} { theorems, config }
        if step.expr == goalType then
          throwError "cnsimp made no progress"
        suggestSimpOnly state tk stx
        liftMetaTactic (applyCnSimpIffResult · goalType step))
      (failed := fun _ => throwError "cnsimp made no progress")
  | _ => throwUnsupportedSyntax

def evalCnSimpa (goal : MVarId) (expr? : Option Expr) : CnSimp.CnSimpM Unit := do
  let goalType ← instantiateMVars (← goal.getType)
  let step ← CnSimp.cnsimp (mkConst ``Iff) goalType
  let mut goal := goal
  if step.expr != goalType then
    let newGoal :: _ ← applyCnSimpIffResult goal goalType step |
      logWarning "unused cnsimpa"
      return
    goal := newGoal
  if let some expr := expr? then
    let type ← inferType expr
    let step ← CnSimp.cnsimp (mkConst ``Iff) type
    let goalType ← goal.getType
    let newType := step.expr
    unless ← isDefEq goalType newType do
      let msg := MessageData.ofLazyM (es := #[goalType, newType]) do
        let (a, b) ← addPPExplicitToExposeDiff goalType newType
        return m!"type mismatch, target{indentExpr a}\nis not definitionally equivalent to{indentExpr b}"
      throwTacticEx `cnsimpa goal msg
    let proof :=
      match step with
      | { proof? := none, .. } => expr
      | { proof? := some prf, .. } => mkApp4 (.const ``Iff.mp []) type newType prf expr
    if newType.isFalse then
      goal.assignFalseProof proof
    else
      goal.assign proof
  else
    goal.assumption

elab_rules : tactic | `(tactic| cnsimpa $cfg:optConfig $(_disch?)? $[only%$only]? $[[$lemmas,*]]? $[using $term]?) => do
  let config ← elabCnSimpConfig cfg
  let mut theorems : SimpTheorems := {}
  if only.isNone then
    theorems ← cnsimpExt.getTheorems
  let goal ← getMainGoal
  goal.withContext do
    let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
    let term ← term.mapM (fun a => elabTerm a none)
    (evalCnSimpa goal term).run' {} { theorems, config }

@[tactic cnsimpaTraceTac]
def evalCnSimpaTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| cnsimpa?%$tk $cfg:optConfig $(_disch?)? $[only%$only]? $[[$lemmas,*]]? $[using $term]?) => do
    let config ← elabCnSimpConfig cfg
    let mut theorems : SimpTheorems := {}
    if only.isNone then
      theorems ← cnsimpExt.getTheorems
    let goal ← getMainGoal
    goal.withContext do
      let theorems ← CnSimp.addCnSimpLemmas (lemmas.elim #[] (·.getElems)) theorems
      let term ← term.mapM (fun a => elabTerm a none)
      let ((), state) ← (evalCnSimpa goal term).run {} { theorems, config }
      suggestSimpOnly state tk stx
  | _ => throwUnsupportedSyntax
