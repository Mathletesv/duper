module

public import Batteries.Data.UnionFind
public import Duper.RuleM
public import Duper.ProverM
public import Duper.MClause
public import Duper.Util.ProofReconstruction

public section

set_option linter.unusedVariables false

namespace Duper
open RuleM
open Lean
open Meta
open ProverM

initialize Lean.registerTraceClass `duper.rule.split

theorem add_imp (a : Prop) (h : a) : ∃ p : Bool, (p → a) ∧ (¬p → False) := by
  apply Exists.intro true
  apply And.intro
  · intros
    exact h
  · intro np
    exact False.elim (np rfl)

-- this is just not possible lmao, p is meaningless outside of the ∃
theorem extraction (x y : Prop) (h : ∃ p : Bool, (p → x) ∧ (¬p → y)) : ∃ p : Bool, (p → x) := by
  sorry

-- state 1: ∃ p : Bool, (p → c1) ∧ (¬ p → c2)

-- inference rule says c1 → c1'

-- state 2: ∃ p : Bool, (p → c1) ∧ (¬ p → c2) ∧ (p → c1')

set_option pp.all true in
theorem split2 (x y : Prop) (h : x ∨ y) : ∃ p : Bool, (p → x) ∧ (p = false → y) := by
  apply Or.elim h
  · intro x
    apply Exists.intro true
    apply And.intro
    · intro
      exact x
    · intro f
      exact Bool.noConfusion f
  · intro y
    apply Exists.intro false
    apply And.intro
    · intro f
      exact Bool.noConfusion f
    · intro
      exact y

theorem natural_split (h0 : a) (h1 : a → b ∨ c) (h2 : b → False) (h3 : c → False) : False := by
  have c1 := h1 h0
  cases c1 with
  | inl hb => exact h2 hb
  | inr hc => exact h3 hc

#print natural_split

theorem full_splitting (a b c d e f : Prop) (h1 : a → b ∨ c) (h2 : b → d) (h3 : d → e) (h4 : c → f)
  (h5 : f → False) (h6 : e → False) : a → False := by
  intro x
  have c1 := h1 x
  have c2 := split2 b c c1
  obtain ⟨p, hb, hc⟩ := c2
  cases p
  · have c3 := hc rfl
    have c4 := h4 c3
    exact h5 c4
  · have c3 := hb rfl
    have c4 := h2 c3
    have c5 := h3 c4
    exact h6 c5

#print full_splitting

theorem full_splitting2 (a b c d e f : Prop) (h1 : a → b ∨ c) (h2 : b → d) (h3 : d → e) (h4 : c → f)
  (h5 : f → False) (h6 : e → False) : a → False := by
  intro x
  have c1 := h1 x
  have c2 := split2 b c c1
  have c3 : b → False := by
    intro y
    have c4 := h2 y
    have c5 := h3 c4
    exact h6 c5
  have c4 : c → False := by
    intro y
    have c5 := h4 y
    exact h5 c5
  obtain ⟨p, hb, hc⟩ := c2
  cases p
  · exact c4 (hc rfl)
  · exact c3 (hb rfl)

#print full_splitting2

theorem split_test3 (x y z : Prop) (h : x ∨ y ∨ z) : ∃ p q : Bool, (p → x) ∧ (q → y) ∧ (p = false ∧ q = false → z) := by
  apply Or.elim h
  · intro x
    apply Exists.intro true
    apply Exists.intro false
    apply And.intro
    · intro
      exact x
    · apply And.intro
      · intro f
        exact Bool.noConfusion f
      · intro f
        exact Bool.noConfusion f.1
  · intro yz
    apply Or.elim yz
    · intro y
      apply Exists.intro false
      apply Exists.intro true
      apply And.intro
      · intro f
        exact Bool.noConfusion f
      · apply And.intro
        · intro
          exact y
        · intro f
          exact Bool.noConfusion f.2
    · intro z
      apply Exists.intro false
      apply Exists.intro false
      apply And.intro
      · intro f
        exact Bool.noConfusion f
      · apply And.intro
        · intro f
          exact Bool.noConfusion f
        · intro
          exact z

theorem full_splitting3 (a b c d e f : Prop) (h1 : a → b ∨ c ∨ d) (h2 : b → e) (h3 : d → e) (h4 : c → f)
  (h5 : f → False) (h6 : e → False) : a → False := by
  intro x
  have c1 := h1 x
  have c2 := split_test3 b c d c1
  have c3 : b → False := by
    intro b
    exact h6 (h2 b)
  have c4 : d → False := by
    intro d
    exact h6 (h3 d)
  have c5 : c → False := by
    intro c
    exact h5 (h4 c)
  obtain ⟨p, q, hb, hc, hd⟩ := c2
  -- match p, q with
  cases p
  · cases q
    · exact c4 (hd ⟨rfl, rfl⟩)
    · exact c5 (hc rfl)
  · exact c3 (hb rfl)

-- set_option pp.all true in
#print full_splitting3

def mkExistsFVars (xs : Array Expr) (body : Expr) : MetaM Expr :=
  xs.foldrM (fun x acc => do
    let α ← inferType x
    let u ← getLevel α
    return mkApp2 (.const ``Exists [u]) α (← mkLambdaFVars #[x] acc)
    ) body

def foldAnd (xs : Array Expr) : MetaM Expr := do
  xs.pop.foldrM (fun x acc => mkAppM ``And #[x, acc]) xs.back!

-- def mkClausesConjunction (clusters : Std.HashMap Nat (Std.HashSet Nat)) (c : Clause) : ProverM Expr := do
--   let mut clauseList := []
--   for (rep, litIdxs) in clusters do
--     let mut lits := (litIdxs.toList).map (fun idx => c.lits[idx]!)
--     let litsOr := Clause.litsToExpr lits
--     clauseList := litsOr :: clauseList
--   let clauseArray := clauseList.toArray
--   let names := (Array.range' 0 (clauseArray.size - 1)).map fun i => Name.mkSimple s!"p{i}"
--   let mut ps := #[]
--   for i in [0:clauseArray.size - 1] do
--     let fvarId ← mkFreshFVarId
--     let lctx' := (← getLCtx).mkLocalDecl fvarId (Name.mkSimple s!"p{i}") (mkConst ``Bool)
--     ps := ps.push (Expr.fvar fvarId)
--     addAssertionFVar fvarId
--   trace[duper.rule.split] "ps: {ps}"
--   let mut clauses := []
--   for idx in [:clauseArray.size - 1] do
--     clauses := (← mkArrow (← mkEq ps[idx]! (mkConst ``Bool.true)) clauseArray[idx]!) :: clauses
--   clauses := (← mkArrow (← foldAnd (← ps.mapM (fun p => return ← mkEq p (mkConst ``Bool.false)))) clauseArray[clauseArray.size - 1]!) :: clauses
--   mkExistsFVars ps (← foldAnd clauses.toArray)
--   -- withLocalDeclsD (names.map fun n => (n, fun _ => pure (mkConst ``Bool))) fun ps => do
--   --   trace[duper.rule.split] "ps: {ps}"
--   --   let mut clauses := []
--   --   for idx in [:clauseArray.size - 1] do
--   --     clauses := (← mkArrow (← mkEq ps[idx]! (mkConst ``Bool.true)) clauseArray[idx]!) :: clauses
--   --   clauses := (← mkArrow (← foldAnd (← ps.mapM (fun p => return ← mkEq p (mkConst ``Bool.false)))) clauseArray[clauseArray.size - 1]!) :: clauses
--   --   mkExistsFVars ps (← foldAnd clauses.toArray)

-- def mkSplitClausesProof (clusters : Std.HashMap Nat (Std.HashSet Nat)) (premises : List Expr) (parents : List ProofParent)
--   (transferExprs : Array Expr) (c : Clause) : ProverM Expr := do
--   let mainClause ← mkClausesConjunction clusters parents[0]!.clause
--   let proof ← mkFreshExprMVar mainClause
--   proof.mvarId!.assign sorry
--   return proof
  -- Meta.lambdaTelescope mainClause fun xs body => do
  --   let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
  --   let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
  --   let parentLits := parentsLits[0]!
  --   let appliedPremise := appliedPremises[0]!
  --   let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
  --   for i in [:parentLits.size] do
  --     let lit := parentLits[i]!
  --     let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
  --       Meta.mkLambdaFVars #[h] $ sorry
  --     proofCases := proofCases.push proofCase
  --   let proof ← orCases (parentLits.map Lit.toExpr) proofCases
  --   Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

def mkSplitClausesProof (c1Lits c2Lits : Array Lit) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  let combinedOr := mkApp2 (mkConst ``Or) (Clause.litsToExpr c1Lits.toList) (Clause.litsToExpr c2Lits.toList)
  let fullClause := c.bVarTypes.foldr (fun ty b => mkForall Name.anonymous BinderInfo.default ty b) combinedOr
  Meta.forallTelescope fullClause fun xs body => do
    let c1Lits := c1Lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let c2Lits := c2Lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if c1Lits.contains lit then
        let j := c1Lits.findIdx (fun l => l == lit)
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← splitOrIntroLeft c1Lits c2Lits j h
        proofCases := proofCases.push proofCase
      else -- `lit` is not the equality to be removed
        let j := c2Lits.findIdx (fun l => l == lit)
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← splitOrIntroRight c1Lits c2Lits j h
        proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

def mkSplitProof (litIdxs : Std.HashSet Nat) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
        Meta.mkLambdaFVars #[h] $ sorry
      proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

-- **TODO**: Figure out how to provide the proof for the multiple clauses
-- The actual clause creation is easy
def splitWithLits (given : Clause) (c : MClause) (clusters : Std.HashMap Nat (Std.HashSet Nat)) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx $ do
    let ug ← unifierGenerator #[]
    let loaded ← getLoadedClauses
    let mut clauses := []
    let mut litArrays := Array.mkEmpty 2
    for (rep, litIdxs) in clusters do
      litArrays := litArrays.push $ (litIdxs.toArray).map (fun idx => c.lits[idx]!)
    let splitProof := mkSplitClausesProof litArrays[0]! litArrays[1]!
    let fvarId ← mkFreshFVarId
    let lctx' := (← getLCtx).mkLocalDecl fvarId (Name.mkSimple s!"p") (mkConst ``Bool)
    let mut splitLit := SplitLit.mk fvarId false
    for (rep, litIdxs) in clusters do
      let mut lits := (litIdxs.toArray).map (fun idx => c.lits[idx]!)
      let yC := do
        setLoadedClauses loaded
        let newMC := MClause.mk lits
        yieldSplitClause splitLit newMC "split" none splitProof --$ mkSplitProof litIdxs
      clauses := (ClauseStream.mk ug given yC "split") :: clauses
      splitLit := SplitLit.mk fvarId true
    -- return #[ClauseStream.mk ug given yC "split"]
    return clauses.toArray


def collectFVars (e : Expr) : RuleM (Array FVarId) := do
  -- trace[duper.rule.split] "Recursing on {e}"
  match e with
  -- | .const declName us => return #[declName]
  | .app fn arg => return (← collectFVars fn) ++ (← collectFVars arg)
  | .lam binderName binderType body _ => return (← collectFVars body)
  | .forallE binderName binderType body _ => return (← collectFVars body)
  | .letE declName type value body _ => return (← collectFVars value) ++ (← collectFVars body)
  | .fvar fvarId => return #[fvarId]
  | _ =>
    -- trace[duper.rule.split] "{e} is here"
    return #[]

def split (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[duper.rule.split] "Split inferences with {c.lits}"
  if c.lits.size < 2 then return #[]
  let mut constIn : Std.HashMap FVarId Nat := {}
  let mut constUf := Batteries.UnionFind.mkEmpty c.lits.size
  let mut streams := #[]
  for _ in [:c.lits.size] do
    constUf := constUf.push
  for i in [:c.lits.size] do
    let lhsConsts ← collectFVars c.lits[i]!.lhs
    let rhsConsts ← collectFVars c.lits[i]!.rhs
    for name in lhsConsts do
      if not (constIn.contains name) then
        trace[duper.rule.split] "New name: {Expr.fvar name} in lit {i}"
        constIn := constIn.insert name i
      else
        trace[duper.rule.split] "Old name: {Expr.fvar name} in lit {i}"
        constUf := constUf.union! (constIn[name]!) i
    for name in rhsConsts do
      if not (constIn.contains name) then
        constIn := constIn.insert name i
        trace[duper.rule.split] "New name: {Expr.fvar name} in lit {i}"
      else
        trace[duper.rule.split] "Old name: {Expr.fvar name} in lit {i}"
        constUf := constUf.union! (constIn[name]!) i
    let mut last := -1
  let mut parents := []
  for i in [:c.lits.size] do
    if (constUf.find! i).snd == i then
      parents := i :: parents
  while parents.length > 2 do
    match parents with
    | p :: q :: ps =>
      constUf := constUf.union! p q
      parents := p :: ps
    | _ => break
  let mut clusters : Std.HashMap Nat (Std.HashSet Nat) := {}
  let mut rep := 0
  for i in [:c.lits.size] do
    (constUf, rep) := constUf.find! i
    if not (clusters.contains rep) then
      clusters := clusters.insert rep { i }
    else
      clusters := clusters.insert rep ((clusters[rep]!).insert i)
  if clusters.size > 1 then
    trace[duper.rule.split] "Can split into {clusters.size} clauses"
    if ← getSplitM then
      return ← splitWithLits given c clusters
  return streams

end Duper
