module

public import Duper.RuleM
public import Duper.ProverM
public import Duper.MClause
public import Duper.Util.ProofReconstruction

public section

namespace Duper
open RuleM
open Lean
open Meta
open ProverM

def unsat (one two : Clause) (c : MClause) : RuleM (Array ClauseStream) := withoutModifyingMCtx $ do
  let assertions := match one.assertions with
    | p :: ps => ps
    | [] => []
  if two.assertions.length != one.assertions.length then return #[]
  let two ← loadClause two
  let ug ← unifierGenerator #[]
  let loaded ← getLoadedClauses
  trace[debug] "Loaded in unsat: {loaded.size}"
  let yC := do
    setLoadedClauses loaded
    some <$> yieldEmptyClause assertions c "unsat" none
  trace[debug] "Proven by unsat for lits: {assertions.length}"
  return #[ClauseStream.mk ug one yC "unsat"]
