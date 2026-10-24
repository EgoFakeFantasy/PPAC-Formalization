import PPAC.Migration.Internal.OriginalAxiomExprQuery
import PPAC.Migration.Internal.LogicalStaticQueries
import YesMetaZFC.Automation.ObjectProofNode

/-! 原theoryShape参数化对象测试节点；专用ZF/U测试尚未实例化。 -/
namespace PPAC.Migration.Internal.ProofTheorySyntax
open Source SourceAlgebra SourceLogic HornExprSyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def formulaExpr : Expr 3 := (ObjectProofNode.theoryShape.queries[0]).2

def axiomExpr : Expr 3 := (ObjectProofNode.theoryShape.queries[1]).2

theorem actual_arity : ObjectProofNode.theoryShape.arity = 3 := rfl

theorem actual_queries : ObjectProofNode.theoryShape.queries = [(.syntax, formulaExpr), (.axiom, axiomExpr)] := rfl

theorem actual_formula : formulaExpr = LogicalStaticQueries.query false 0 1 := rfl

theorem actual_axiom : axiomExpr = ObjectProofNode.node 0 [.var 2, .var 1] := rfl

def axiomFields {m} (env : Fin 3 → Fin m) : Fin 2 → Fin m :=
  Fin.cases (env 2) (Fin.cases (env 1) Fin.elim0)

def bundle {m} (test : Formula 1) (w : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query formulaExpr w env).conj (OriginalAxiomExprQuery.query test axiomExpr w env)

def specification {m} (test : Formula 1) (w z : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) z (env 0)).conj (OriginalAxiomExprQuery.rowQuery test 2 0 w (axiomFields env))

end PPAC.Migration.Internal.ProofTheorySyntax
