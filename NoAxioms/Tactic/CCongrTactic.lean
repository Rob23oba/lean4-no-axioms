import NoAxioms.Tactic.CongrSimpExt
import Lean.Elab.Tactic

open Lean Meta Elab Tactic

namespace CCongr

def tryCongrOneSimple (goal : MVarId) (c : CCongrTheorem) (p : SimpleCCongrProcedure) : MetaM (Option (List MVarId)) := withReducible do
  trace[Meta.Tactic.simp.congr] m!"try simple congruence {c.thmName} on {goal.name} of type {← goal.getType}"
  let goalType ← goal.getType'
  let goalType := goalType.consumeMData
  let mkApp2 rel lhs rhs := goalType | unreachable!
  let lhsArgs := lhs.getAppArgs'
  if lhsArgs.size != p.arity then
    trace[Meta.Tactic.simp.congr] m!"arity mismatch on lhs {lhsArgs.size} and {p.arity}"
    return none
  let rhsArgs := rhs.getAppArgs'
  if rhsArgs.size != p.arity then
    trace[Meta.Tactic.simp.congr] m!"arity mismatch on rhs {rhsArgs.size} and {p.arity}"
    return none
  let relArgs := rel.getAppArgs'
  let args := relArgs ++ lhsArgs
  let levels := lhs.getAppFn'.constLevels!
  let lparams := p.lparamPerm.map (levels[·]!)
  let mut params : Array Expr := #[]
  let mut goals := []
  for param in p.params do
    match param with
    | .relParam i =>
      params := params.push relArgs[i]!
    | .preParam i | .fixed i =>
      params := params.push lhsArgs[i]!
    | .postParam i synth =>
      if h : i < rhsArgs.size then
        params := params.push rhsArgs[i]
      else
        match synth with
        | .synth cls =>
          try
            let newClass := (cls.instantiateRev params).instantiateLevelParamsCore
              (fun n => match n with | .num _ n => levels[n]! | _ => none)
            let inst ← synthInstance newClass
            params := params.push inst
          catch e =>
            trace[Meta.Tactic.simp.congr] m!"discharge failed: {cls}"
            return none
        | .exact expr =>
          let newExpr := (expr.instantiateRev params).instantiateLevelParamsCore
            (fun n => match n with | .num _ n => levels[n]! | _ => none)
          params := params.push newExpr
        | .none =>
          trace[Meta.Tactic.simp.congr] m!"invalid parameter but no discharger"
          return none
    | .rel rel' i =>
      let newRel := (rel'.instantiateRev args).instantiateLevelParamsCore
        (fun n => match n with | .num _ n => levels[n]! | _ => none)
      let newGoalType := mkApp2 newRel lhsArgs[i]! rhsArgs[i]!
      let newGoal ← mkFreshExprMVar newGoalType
      goals := newGoal.mvarId! :: goals
      params := params.push newGoal
  let proof : Expr := mkAppN (Expr.const c.thmName lparams) params
  trace[Meta.Tactic.simp.congr] m!"constructed proof {proof}"
  goal.assign proof
  return some goals

def tryCongrOneNewSimple (goal : MVarId) (c : CCongrTheorem) (p : NewSimpleCongr) : MetaM (Option (List MVarId)) := withReducible do
  trace[Meta.Tactic.simp.congr] m!"try new simple congruence {c.thmName} on {goal.name} of type {← goal.getType}"
  let goalType ← goal.getType'
  let goalType := goalType.consumeMData
  let mkApp2 rel lhs rhs := goalType | unreachable!
  let lhsArgs := lhs.getAppArgs'
  if lhsArgs.size != p.funArity then
    trace[Meta.Tactic.simp.congr] m!"arity mismatch on lhs {lhsArgs.size} and {p.funArity}"
    return none
  let rhsArgs := rhs.getAppArgs'
  if rhsArgs.size != p.funArity then
    trace[Meta.Tactic.simp.congr] m!"arity mismatch on rhs {rhsArgs.size} and {p.funArity}"
    return none
  let mut state : Array Expr := Array.replicate p.proofArity default
  try
    state ← traverseNewTypes rel p.relArgsIterate state
    state ← traverseNewTypes lhs p.lhsArgsIterate state
    state ← traverseNewTypes rhs p.rhsArgsIterate state
  catch e =>
    trace[Meta.Tactic.simp.congr] e.toMessageData
    return none
  let levels := lhs.getAppFn'.constLevels!
  let lparams := p.lparamsPerm.map (levels[·]!)
  let mut goals := []
  let lfun (n : Name) : Option Level := match n with | .num _ n => levels[n]! | _ => none
  for act in p.preActions do
    match act with
    | .synth nec i type =>
      unless nec do
        continue
      let type := (type.instantiate state).instantiateLevelParamsCore lfun
      try
        let expr ← synthInstance type
        state := state.set! i expr
      catch _ =>
        trace[Meta.Tactic.simp.congr] m!"discharge failed"
        return none
    | .exact .. => continue
    | .introMVar i type =>
      let type := (type.instantiate state).instantiateLevelParamsCore lfun
      let mvar ← mkFreshExprMVar type
      state := state.set! i mvar
    | .rel i lhs rhs rel =>
      let rel := (rel.instantiate state).instantiateLevelParamsCore lfun
      let goalType := mkApp2 rel state[lhs]! state[rhs]!
      let goal ← mkFreshExprSyntheticOpaqueMVar goalType
      state := state.set! i goal
      goals := goal.mvarId! :: goals
  let proof : Expr := mkAppN (Expr.const c.thmName lparams) state
  trace[Meta.Tactic.simp.congr] m!"constructed proof {proof}"
  goal.assign proof
  return some goals

def tryCongrOne (goal : MVarId) (c : CCongrTheorem) (pos : Array Nat) : MetaM (Option (List MVarId)) := withReducible do
  trace[Meta.Tactic.simp.congr] m!"try congruence {c.thmName} on {goal}"
  let goalType ← goal.getType'
  let some const := (← getEnv).findConstVal? c.thmName | return none
  let levels ← mkFreshLevelMVars const.levelParams.length
  let type := const.type.instantiateLevelParams const.levelParams levels
  let (xs, _, type) ← forallMetaTelescopeReducing type
  unless ← isDefEq goalType type do
    return none
  let mut goals := []
  for i in pos do
    let goal := xs[i]!.mvarId!
    if ← goal.isAssigned then
      continue
    let type ← goal.getType'
    let (expr, newGoal) ← forallTelescope type fun fvars newType => do
      let goal ← mkFreshExprSyntheticOpaqueMVar newType
      let proof ← mkLambdaFVars fvars goal
      return (proof, goal.mvarId!)
    goal.assign expr
    goals := newGoal :: goals
  for x in xs do
    let mvar := x.mvarId!
    unless ← mvar.isAssigned do
      try
        mvar.inferInstance
      catch _ =>
        trace[Meta.Tactic.simp.congr] m!"discharge failed"
        return none
  let proof : Expr := .const c.thmName levels
  let proof := mkAppN proof xs
  goal.assign proof
  return some goals

def forallCongr (goal : MVarId) (lhs rhs : Expr) : MetaM (Option (List MVarId)) := do
  let .forallE nm t b bi := lhs | return none
  let .forallE _ t' b' _ := rhs | return none
  let lvl ← getLevel t
  if ← isDefEq t t' then
    let goalType : Expr := .forallE nm t (mkApp2 (mkConst ``Iff) b b') bi
    forallTelescope goalType fun fvars goalType' => do
      let newGoal ← mkFreshExprSyntheticOpaqueMVar goalType'
      let proof ← mkLambdaFVars fvars newGoal
      let proof := mkApp4 (.const ``forall_congr' [lvl]) t (.lam nm t b bi) (.lam nm t b' bi) proof
      goal.assign proof
      return some [newGoal.mvarId!]
  else if lvl.isAlwaysZero then
    let lhsIff : Expr := mkApp2 (mkConst ``Iff) t t'
    let goal1 ← mkFreshExprSyntheticOpaqueMVar lhsIff
    let goalType : Expr := .forallE nm t (mkApp2 (mkConst ``Iff) b b') bi
    forallTelescope goalType fun fvars goalType' => do
      let newGoal ← mkFreshExprSyntheticOpaqueMVar goalType'
      let proof ← mkLambdaFVars fvars newGoal
      let proof := mkApp6 (.const ``forall_prop_congr []) t t' (.lam nm t b bi) (.lam nm t b' bi) goal1 proof
      goal.assign proof
      return some [goal1.mvarId!, newGoal.mvarId!]
  else
    return none

def tryCongrs (goal : MVarId) : MetaM (Option (List MVarId)) := do
  let goalType ← goal.getType'
  let goalType := goalType.consumeMData
  let mkApp2 rel lhs rhs := goalType | return none
  unless rel.getAppFn'.isConst do
    return none
  if ← isDefEq lhs rhs then
    let relName := rel.getAppFn'.constName!
    if ((← getEnv).findAsync? (.str relName "refl")).isSome then
      goal.assign (← mkAppM (.str relName "refl") #[lhs])
      return some []
    return none
  if rel.isConstOf ``Iff ∧ lhs.isForall ∧ rhs.isForall then
    return ← forallCongr goal lhs rhs
  let app := lhs.getAppFn'
  let app' := rhs.getAppFn'
  unless app.isConst && app'.isConst do
    trace[Meta.Tactic.simp.congr] m!"not consts, {app} {app'}"
    return none -- not supported currently
  unless app.constName! == app'.constName! do
    trace[Meta.Tactic.simp.congr] m!"not the same consts, {app} {app'}"
    return none
  let relName := rel.getAppFn'.constName!
  let state := ccongrExtension.getState (← getEnv)
  let some congr := state.lemmas.find? { rel := relName, decl := app.constName! } |
    trace[Meta.Tactic.simp.congr] m!"no lemma, {relName} {app}"
    return none
  for c in congr do
    let goals ← match c.procedure with
    | .expensiveProcedure p => tryCongrOne goal c p
    | .simpleProcedure p => tryCongrOneSimple goal c p
    | .newSimpleProcedure p => tryCongrOneNewSimple goal c p
    if goals.isSome then
      return goals
  return none

def congrOften (goal : MVarId) (max? : Option Nat) : MetaM (List MVarId) := do
  let mut rounds := 0
  let mut goalsToProcess := [goal]
  let mut nextGoals := []
  let mut finalGoals := []
  while !goalsToProcess.isEmpty && max?.all (rounds < ·) do
    for goal in goalsToProcess do
      let some c ← goal.withContext <| tryCongrs goal | finalGoals := goal :: finalGoals
      nextGoals := c.reverseAux nextGoals
    goalsToProcess := nextGoals
    nextGoals := []
    rounds := rounds + 1
  return finalGoals.reverseAux goalsToProcess

end CCongr

elab "ccongr" use:(&"using" num)? : tactic => do
  let goal ← getMainGoal
  withReducible do
    let goals ← CCongr.congrOften goal (use.map (fun _ => 1))
    replaceMainGoal goals

elab "ccongr1" : tactic => do
  let goal ← getMainGoal
  withReducible do
    let goals ← CCongr.congrOften goal (some 1)
    replaceMainGoal goals
