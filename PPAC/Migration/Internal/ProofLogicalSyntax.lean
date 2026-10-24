import PPAC.Migration.Internal.OriginalLogicalExprQuery
import YesMetaZFC.Automation.ObjectProofNode

/-! 原logicalShape准确字段换位；接受查询使用原27模式表，独立规格使用数值头与数学表。 -/
namespace PPAC.Migration.Internal.ProofLogicalSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def queryExpr : Expr 3 := (ObjectProofNode.logicalShape.queries[0]).2

theorem actual_arity : ObjectProofNode.logicalShape.arity = 3 := rfl

theorem actual_query : ObjectProofNode.logicalShape.queries = [(.logical, queryExpr)] := rfl

theorem actual_query_fields : queryExpr = ObjectProofNode.node 0 [.var 0, .var 2, .var 1] := rfl

def headFields {m} (env : Fin 3 → Fin m) : Fin 3 → Fin m := env

def queryFields {m} (env : Fin 3 → Fin m) : Fin 3 → Fin m :=
  Fin.cases (env 0) (Fin.cases (env 2) (Fin.cases (env 1) Fin.elim0))

theorem queryFields_map {m l} (env : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (queryFields env i)) = queryFields (fun i => ρ (env i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun q => Fin.elim0 q) k

def bundle {m} (w : Fin m) (env : Fin 3 → Fin m) : Formula m := OriginalLogicalExprQuery.query queryExpr w env

def specification {m} (w z : Fin m) (env : Fin 3 → Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 3 0 w.castSucc (queryFields (fun i => (env i).castSucc)) (Fin.last m)).conj
    (LogicalAllPatterns.specification w.castSucc z.castSucc (Fin.last m)))

end PPAC.Migration.Internal.ProofLogicalSyntax
