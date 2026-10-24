import PPAC.Migration.Internal.LogicalStaticQueries

/-! 实际原有序Bool查询表的合取解释与有限查询bundle逐项一致。 -/
namespace PPAC.Migration.Internal.LogicalStaticQueryList
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation.ObjectHorn (Expr)

def listBundle {m a} : List (Bool × Expr a) → Fin m → (Fin a → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons (flag, expr) rest, w, env =>
      (if flag then OriginalTransformExprQuery.query expr w env else PureSyntaxExprQuery.query expr w env).conj (listBundle rest w env)

theorem finRange_bundle {m a} (n : Nat) (exprs : Fin n → Expr a) (w : Fin m) (env : Fin a → Fin m) :
    listBundle ((List.finRange n).map (fun i => (false, exprs i))) w env =
      LogicalStaticQueries.conjoin n (fun i => PureSyntaxExprQuery.query (exprs i) w env) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.finRange_succ, List.map_cons, List.map_map, listBundle, LogicalStaticQueries.conjoin]
    exact congrArg (Formula.conj (PureSyntaxExprQuery.query (exprs 0) w env)) (ih (fun i => exprs i.succ))

theorem original_bundle {m} (n : Nat) (isTerm : Bool) (w : Fin m) (env : Fin (n+1) → Fin m) :
    listBundle (LogicalStaticQueries.originalQueries n isTerm) w env = LogicalStaticQueries.bundle n isTerm w env :=
  finRange_bundle n (fun i => LogicalStaticQueries.query isTerm 0 i.succ) w env

end PPAC.Migration.Internal.LogicalStaticQueryList
