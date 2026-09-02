import Lean
import Duper.Util.Misc
import Duper.Expr
import Duper.Order

namespace Duper
open Lean
open Lean.Meta

register_option duper.split : Bool := {
  defValue := true
  descr := "Whether to use splitting"
}

def getSplit (opts : Options) : Bool :=
  duper.split.get opts

def getSplitM : CoreM Bool := do
  let opts ← getOptions
  return getSplit opts

structure SplitLit where
  id : FVarId
  sgn : Bool
deriving Inhabited, BEq, Hashable

namespace SplitLit

def toExpr (l : SplitLit) : Expr :=
  match l.sgn with
  | true => mkConst ``true
  | false => mkConst ``false

end SplitLit

end Duper
