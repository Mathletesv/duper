import Lean
import Duper.Saturate

set_option linter.unusedVariables false

open Lean
open Lean.Meta
open Duper
open ProverM

initialize
  registerTraceClass `duper.printProof
  registerTraceClass `duper.proofReconstruction

def getClauseInfo! (state : ProverM.State) (c : Clause) : CoreM ClauseInfo := do
  let some ci := state.allClauses.get? c
    | throwError "clause info not found: {c}"
  return ci

partial def printProof (state : ProverM.State) : MetaM Unit := do
  Core.checkMaxHeartbeats "printProof"
  let rec go c (hm : Array (Nat × Clause) := {}) : MetaM (Array (Nat × Clause)) := do
    let info ← getClauseInfo! state c
    if hm.contains (info.number, c) then return hm
    let mut hm := hm.push (info.number, c)
    for proofParent in info.proof.parents do
      hm ← go proofParent.clause hm
    return hm
  let some emptyClause := state.emptyClause
    | throwError "printProof :: Can't find empty clause in ProverM's state"
  let proofClauses ← go emptyClause
  let proofClauses := proofClauses.qsort (fun (n1, _) => fun (n2, _) => n1 < n2)
  for (_, c) in proofClauses do
    let info ← getClauseInfo! state c
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! state pp.clause)
    let parentIds := parentInfo.map fun info => info.number
    trace[duper.printProof] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    -- println!  s!"Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {toString (← ppExpr c.toForallExpr)}"

abbrev ClauseHeap := Batteries.BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1

partial def collectClauses (state : ProverM.State) (c : Clause) (acc : (Array Nat × ClauseHeap)) : MetaM (Array Nat × ClauseHeap) := do
  Core.checkMaxHeartbeats "collectClauses"
  let info ← getClauseInfo! state c
  if acc.1.contains info.number then return acc -- No need to recall collectClauses on c because we've already collected c
  let mut acc := acc
  -- recursive calls
  acc := (acc.1.push info.number, acc.2.insert (info.number, c))
  for proofParent in info.proof.parents do
    acc ← collectClauses state proofParent.clause acc
  return acc

-- Map from clause `id` to Array of request of levels
abbrev LevelRequests := Std.HashMap Nat (Std.HashMap (Array Level) Nat)

partial def collectLevelRequests (state : ProverM.State) (c : Clause)
  (lvls : Array Level) (acc : LevelRequests) : MetaM LevelRequests := do
  Core.checkMaxHeartbeats "collectLevelRequests"
  let info ← getClauseInfo! state c
  if let some set := acc.get? info.number then
    if set.contains lvls then
      return acc
  let mut acc := acc
  let lvlset :=
    match acc.get? info.number with
    | some set => set
    | none     => Std.HashMap.emptyWithCapacity
  trace[duper.proofReconstruction] "Request {c.paramNames} ↦ {lvls} for {c}"
  acc := acc.insert info.number (lvlset.insert lvls lvlset.size)
  for proofParent in info.proof.parents do
    let lvls' := proofParent.paramSubst.map
      (fun lvl => lvl.instantiateParams c.paramNames.toList lvls.toList)
    acc ← collectLevelRequests state proofParent.clause lvls' acc
  return acc

structure PRContext where
  pmstate : ProverM.State
  reqs  : LevelRequests

structure PRState where
  -- `Nat` is the `id` of the clause
  -- `Array Level` is the requested levels for the clause
  -- `Expr` is the fvarId corresponding to the proof for the clause in the current `lctx`
  constructedClauses : Std.HashMap (Nat × Array Level) Expr
  -- Map from `id` of skolem constant to the constructed `fvar`
  constructedSkolems : Std.HashMap Nat FVarId
  lctx : LocalContext
  mctx : MetavarContext
  localInstances : LocalInstances
  fvars : Array Expr
  holes : Std.HashMap SplitLit MVarId
deriving Inhabited

def PRState.insertConstructedClauses (prs : PRState) (key : Nat × Array Level) (val : Expr) :=
  {prs with constructedClauses := prs.constructedClauses.insert key val}

abbrev PRM := ReaderT PRContext <| StateRefT PRState CoreM

def PRM.addHole (lit : SplitLit) (id : MVarId) : PRM Unit := do
  modify fun s => {s with holes := s.holes.insert lit id}

def PRM.mkLetDecl (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep := false) (kind : LocalDeclKind := default) : PRM Unit := do
  let lctx := (← get).lctx
  let lctx' := lctx.mkLetDecl fvarId userName type value nonDep kind
  modify fun s => {s with lctx := lctx'}
  modify fun s => {s with fvars := s.fvars.push (mkFVar fvarId)}

-- Does not update the metavariable context !
def runMetaAsPRM {α} (x : MetaM α) : PRM α := do
  let lctx := (← get).lctx
  let mctx := (← get).mctx
  let localInstances := (← get).localInstances
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx, localInstances := localInstances}) (s := {mctx := mctx}) do
    x
  modify fun s => {s with mctx := state.mctx}
  return res

def PRM.run (m : PRM α) (ctx : PRContext) (st : PRState) : CoreM (α × PRState) :=
  StateRefT'.run (m ctx) st

private instance : Inhabited TransformStep where
  default := TransformStep.continue

partial def PRM.matchSkolem : Expr → PRM TransformStep
| e@(.app ..) => e.withApp fun f args => do
  let (.const skName lvl) := f
    | return .continue
  let skolemSorryName := (← read).pmstate.skolemSorryName
  if skName == skolemSorryName then
    let opqn := args[0]!
    let lvls ← runMetaAsPRM <| RuleM.unWrapSort opqn
    let .natVal skid := args[1]!.litValue!
      | throwError "PRM.matchSkolem :: Invalid skolem id!"
    let skTy := args[2]!
    let skmap := (← read).pmstate.skolemMap
    let consk := (← get).constructedSkolems
    if let some isk := skmap.get? skid then
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      if let some fvarId := consk.get? skid then
        return .done (mkAppN (mkFVar fvarId) trailingArgs)
      let ⟨skProof, params⟩ := isk
      let skProof := skProof.instantiateLevelParamsArray params lvls
      let skProof ← Core.transform skProof PRM.matchSkolem
      -- Don't need to instantiate level params for `skTy`, because
      --   it's already instantiated
      let skTy ← Core.transform skTy PRM.matchSkolem
      let fvarId ← mkFreshFVarId
      let userName := Name.num `skol skid
      PRM.mkLetDecl fvarId userName skTy skProof
      runMetaAsPRM <| do
        trace[duper.proofReconstruction] "Reconstructing skolem, {(mkFVar fvarId).dbgToString} ≡≡ {mkFVar fvarId} : {skTy} := {skProof}"
      modify fun s => {s with constructedSkolems := s.constructedSkolems.insert skid fvarId}
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      return .done (mkAppN (mkFVar fvarId) trailingArgs)
    else
      throwError "PRM.matchSkolem :: Unable to find skolem {skid} in skolem map!"
  else
    return .continue
| _ => return .continue

theorem natural_split (h0 : a) (h1 : a → b ∨ c) (h2 : b → False) (h3 : c → False) : False := by
  have c1 := h1 h0
  cases c1 with
  | inl hb =>
    have c2 := hb
    have c3 := c2
    exact h2 c3
  | inr hc => exact h3 hc

#print natural_split

theorem natural_split_term.{u_1} : ∀ {a : Sort u_1} {b c : Prop} (h0 : a),
  (∀ (a : a), b ∨ c) → (b → False) → (c → False) → False :=
  fun h0 h1 h2 h3 =>
    have c1 := h1 h0;
    Or.elim c1 (fun hb => h2 hb) (fun hc => h3 hc)

theorem split_tactic (h0 : a) (h1 : a → b ∨ c) (h2 : b → False) (h3 : c → False) : False := by
  have c1 := h1 h0
  apply Or.elim c1
  · exact h2
  · exact h3

#print split_tactic

/-
Use tree like chaining to open a cases at a split and then
derive false in that branch with a single mkClauseProof recursive chain
And do another recursive chain for the other case

Note that all clauses after the split can just be proven
in each chain as necessary, since there is no inter-chain connection allowed
for this version of splitting

This should be the simplest method, it just requires going until the first unsat
Split-unsat pairs work the way parenthesis work, so the logic is very natural
False is actually always reached before unsat, so the unsat rule should just be ignored
-/

partial def mkClauseProof : List Clause → List SplitLit → PRM Expr
| [], _ => panic! "mkClauseProof :: empty clause list"
| c :: cs, ps => do
  if !(Clause.assertionSubset c.assertions ps) && !(Clause.assertionSubset ps c.assertions) then
    return ← mkClauseProof cs ps
  let state := (← read).pmstate
  let reqs := (← read).reqs
  Core.checkMaxHeartbeats "mkClauseProof"
  let info ← getClauseInfo! state c
  if info.proof.ruleName == "unsat" then
    return ← mkClauseProof cs ps
  let lvlreqs := reqs.get! info.number
  for (req, reqid) in lvlreqs.toList do
    trace[duper.proofReconstruction] "lvlReqs : {lvlreqs.toList}, req: {req}"
    let mut parents : Array Expr := #[]
    let mut parentClauses : Array Clause := #[]
    let mut instantiatedProofParents := #[]
    for parent in info.proof.parents do
      let parentInfo ← getClauseInfo! state parent.clause
      let parentNumber := parentInfo.number
      let instantiatedParentParamSubst := parent.paramSubst.map (fun lvl => lvl.instantiateParams c.paramNames.toList req.toList)
      let parentPrfFvar := (← get).constructedClauses.get! (parentNumber, instantiatedParentParamSubst)
      parents := parents.push parentPrfFvar
      runMetaAsPRM <| do
        trace[duper.proofReconstruction] (
          m!"Instantiating parent {parent.clause} ≡≡ {parent.expr} with " ++
          m!"param subst {parent.clause.paramNames} ↦ {instantiatedParentParamSubst}"
        )
      let parentClause := parent.clause.instantiateLevelParamsArray parent.clause.paramNames instantiatedParentParamSubst
      let parentClause ← parentClause.mapMUpdateType (fun e => Core.transform e PRM.matchSkolem)
      parentClauses := parentClauses.push parentClause
      let parentExpr := parent.expr.instantiateLevelParamsArray parentClause.paramNames instantiatedParentParamSubst
      -- We need to instantiate `c`'s params with `req`. This is because universe metavariables
      --   might be introduces during unification
      let parentExpr := parentExpr.instantiateLevelParamsArray c.paramNames req
      let parentExpr ← Core.transform parentExpr PRM.matchSkolem
      let instPP := {parent with expr := parentExpr, clause := parentClause}
      instantiatedProofParents := instantiatedProofParents.push instPP
    -- Now `parents[i] : info.proof.parents[i].toForallExpr`, for all `i`
    let instC := c.instantiateLevelParamsArray c.paramNames req
    let instC ← instC.mapMUpdateType (fun e => Core.transform e PRM.matchSkolem)
    runMetaAsPRM <| do
      trace[duper.proofReconstruction] (
        m!"Reconstructing proof for #{info.number} " ++
        m!": {instC.paramNames} ↦ {req} @ {instC}, Rule Name: {info.proof.ruleName}"
      )
    let newTarget := instC.toForallExpr
    if info.proof.ruleName == "split" then
      match c.assertions with
      | p :: _ =>
        let some splitProof := info.proof.mkSplitProof
        | throwError "no split proof when necessary"
        let instTr := info.proof.transferExprs.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
        let instTr ← instTr.mapM (fun e => Core.transform e PRM.matchSkolem)
        let prf ← runMetaAsPRM <|
          splitProof parents.toList instantiatedProofParents.toList instTr instC
        let split := prf
        -- let h := split
        -- let hb := newTarget
        -- let hc ← sorry
        -- let bodyOne ← mkClauseProof cs (p::ps)
        -- let bodyTwo ← mkClauseProof cs ({p with sgn := !p.sgn}::ps)

              -- `split : b ∨ c`
        let splitType ← runMetaAsPRM <| inferType split

        let .app (.app (.const ``Or _) b) c := splitType
          | throwError "split proof does not have type `Or _ _`"
        let falseTy := mkConst ``False
        -- let caseOne ← withLocalDeclD `hb b fun hb => do
        --     -- Make `hb` visible to the recursive proof search.
        --     --
        --     -- The recursive call sees:
        --     --   ... hb : b
        --     --   ⊢ False
        --     --
        --     -- and can itself create more local lets / split further.
        --     let body ← mkClauseProof cs (p :: ps)

        --     mkLambdaFVars #[hb] body

        -- let caseTwo ← runMetaAsPRM <| do
        --   withLocalDeclD `hc c fun hc => do
        --     let body ← mkClauseProof cs ({p with sgn := !p.sgn} :: ps)

        --     mkLambdaFVars #[hc] body
        -- let caseOne ← runMetaAsPRM <| mkLambdaFVars #[hb] bodyOne
        -- let caseTwo ← runMetaAsPRM <| mkLambdaFVars #[hc]
        let caseOne ← runMetaAsPRM <| mkFreshExprMVar (← mkArrow b falseTy) .syntheticOpaque
        runMetaAsPRM <| caseOne.mvarId!.assign sorry
        let caseTwo ← runMetaAsPRM <| mkFreshExprMVar (← mkArrow c falseTy) .syntheticOpaque
        runMetaAsPRM <| caseTwo.mvarId!.assign sorry
        let proof ← runMetaAsPRM <| mkAppM ``Or.elim #[split, caseOne, caseTwo]
        return proof
      | _ => throwError "Created a split clause with no assertions!"
      -- let hole ← runMetaAsPRM <| mkFreshExprMVar newTarget .syntheticOpaque
      -- match c.assertions with
      -- | p :: _ => PRM.addHole p hole.mvarId! -- get splitlit here
      -- | _ => throwError "Created a split clause with no assertions!"
      -- runMetaAsPRM <|
      --   do trace[duper.proofReconstruction] "#{info.number} added as split clause"
      -- -- Add the new proof to the local context
      -- let fvarId ← mkFreshFVarId
      -- let declName := (Name.mkNum (Name.mkNum `clause info.number) reqid)
      -- PRM.mkLetDecl fvarId declName newTarget hole
      -- modify fun ctrc => ctrc.insertConstructedClauses (info.number, req) (mkFVar fvarId)
    -- else if info.proof.ruleName == "unsat" then
    --   match parentClauses[0]!.assertions, parentClauses[1]!.assertions with
    --   | p :: _, q :: _ =>
    --     let s ← get
    --     let mvarOne := s.holes.get! p
    --     let mvarTwo := s.holes.get! q

    --   | _, _ => throwError "Unsat parent doesn't have an assertion!"
    else
      let instTr := info.proof.transferExprs.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
      let instTr ← instTr.mapM (fun e => Core.transform e PRM.matchSkolem)
      let newProof ← (do
        let prf ← runMetaAsPRM <|
          info.proof.mkProof parents.toList instantiatedProofParents.toList instTr instC
        if info.proof.ruleName != "assumption" then
          return prf
        else
          -- If the rule is "assumption", then there is no proofparent and
          --   we have to manually instantiate the universe mvars
          return prf.instantiateLevelParamsArray c.paramNames req)
      runMetaAsPRM <|
        do trace[duper.proofReconstruction] "#{info.number}'s newProof: {newProof}"
      if cs == [] then return newProof
      -- Add the new proof to the local context
      let fvarId ← mkFreshFVarId
      let declName := (Name.mkNum (Name.mkNum `clause info.number) reqid)
      PRM.mkLetDecl fvarId declName newTarget newProof
      modify fun ctrc => ctrc.insertConstructedClauses (info.number, req) (mkFVar fvarId)
  mkClauseProof cs ps

partial def mkAllProof (state : ProverM.State) (cs : List Clause) : MetaM Expr := do
  let cs := Array.mk cs
  let cslen := cs.size
  if cslen == 0 then
    throwError "mkClauseProof :: Empty Clause List"
  -- The final empty clause
  let emptyClause := cs[cslen - 1]!
  -- Other clauses
  let zeroLvlsForEmptyClause := emptyClause.paramNames.map (fun _ => Level.zero)
  let reqs ← collectLevelRequests state emptyClause zeroLvlsForEmptyClause Std.HashMap.emptyWithCapacity
  let (e, prstate) ← (do mkClauseProof cs.toList []).run
      {pmstate := state, reqs := reqs}
      {constructedClauses := Std.HashMap.emptyWithCapacity, constructedSkolems := Std.HashMap.emptyWithCapacity,
       lctx := ← getLCtx, mctx := ← getMCtx, localInstances := ← getLocalInstances, fvars := #[], holes := {}}
  setMCtx prstate.mctx
  let lctx := prstate.lctx
  let fvars := prstate.fvars
  let abstLet ← withLCtx lctx (← getLocalInstances) do
    mkLambdaFVars (usedLetOnly := false) fvars e
  return abstLet

/-- Given the ProverM state of a duper instance that found a contradiction, reconstruct the proof that duper found
    and return it as an expression. -/
def reconstructProof (state : ProverM.State) : MetaM Expr := do
  let some emptyClause := state.emptyClause
    | throwError "applyProof :: Can't find empty clause in ProverM's state"
  let l := (← collectClauses state emptyClause (#[], Batteries.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[duper.proofReconstruction] "Collected clauses: {l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← mkAllProof state l
  trace[duper.proofReconstruction] "Proof: {proof}"
  return proof
