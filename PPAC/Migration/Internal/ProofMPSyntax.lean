import PPAC.Migration.Internal.ProofProjectionExpr
import PPAC.Migration.Internal.PureProofSubstitutionQueries

/-! 直接取原MP描述符全部六查询；蕴含码读取规格独立于实际接受定义。 -/
namespace PPAC.Migration.Internal.ProofMPSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open ProofSubstitutionProjectionSyntax (atOne atOne_rename)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def conclusionQuery : Expr 5 := (ObjectProofNode.mpShape.queries[0]).2
def antecedentQuery : Expr 5 := (ObjectProofNode.mpShape.queries[1]).2
def leftFreeQuery : Expr 5 := (ObjectProofNode.mpShape.queries[2]).2
def leftFormulaQuery : Expr 5 := (ObjectProofNode.mpShape.queries[3]).2
def rightFreeQuery : Expr 5 := (ObjectProofNode.mpShape.queries[4]).2
def rightImplicationQuery : Expr 5 := (ObjectProofNode.mpShape.queries[5]).2

def implicationFields : Fin 2 → Expr 5 := SetLanguage.args2 (.var 4) (.var 1)
def implicationExpr : Expr 5 := ObjectProofNode.node 7 [.var 4, .var 1]

theorem actual_conclusion : ObjectProofNode.mpShape.queries[0] = ObjectProofNode.formula (.var 0) (.var 1) := rfl
theorem actual_antecedent : ObjectProofNode.mpShape.queries[1] = ObjectProofNode.formula (.var 0) (.var 4) := rfl
theorem actual_leftFree : ObjectProofNode.mpShape.queries[2] = ObjectProofNode.projection (.var 2) 0 (.var 0) := rfl
theorem actual_leftFormula : ObjectProofNode.mpShape.queries[3] = ObjectProofNode.projection (.var 2) 1 (.var 4) := rfl
theorem actual_rightFree : ObjectProofNode.mpShape.queries[4] = ObjectProofNode.projection (.var 3) 0 (.var 0) := rfl
theorem actual_rightImplication : ObjectProofNode.mpShape.queries[5] = ObjectProofNode.projection (.var 3) 1 (ObjectProofNode.node 7 [.var 4, .var 1]) := rfl
theorem actual_implication : implicationExpr = Expr.node (.literal 7) (List.ofFn implicationFields) := rfl

def implicationRead {m} (w p a b : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 2 7 w.castSucc (SetLanguage.args2 a.castSucc b.castSucc) (Fin.last m)).conj
    (atOne w.castSucc p.castSucc (Fin.last m)))

def projections {m} (w : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (ProjectionExprQuery.query leftFreeQuery w env).conj ((ProjectionExprQuery.query leftFormulaQuery w env).conj
    ((ProjectionExprQuery.query rightFreeQuery w env).conj (ProjectionExprQuery.query rightImplicationQuery w env)))

def metadata {m} (w z : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (RawCodeFieldSyntax.field w (env 2) z (env 0)).conj ((atOne w (env 2) (env 4)).conj
    ((RawCodeFieldSyntax.field w (env 3) z (env 0)).conj (implicationRead w (env 3) (env 4) (env 1))))

theorem implicationRead_rename {m l} (w p a b : Fin m) (ρ : Fin m → Fin l) :
    (implicationRead w p a b).rename ρ = implicationRead (ρ w) (ρ p) (ρ a) (ρ b) := by
  simp only [implicationRead, Formula.rename, SyntaxNodeSyntax.constructor_rename, ProjectionTraceSyntax.args2_map,
    atOne_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem projections_rename {m l} (w : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (projections w env).rename ρ = projections (ρ w) (fun j => ρ (env j)) := by
  simp only [projections, Formula.rename, ProjectionExprQuery.query_rename]

theorem metadata_rename {m l} (w z : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (metadata w z env).rename ρ = metadata (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [metadata, Formula.rename, RawCodeFieldSyntax.field_rename, atOne_rename, implicationRead_rename]

theorem intro_implicationRead {m} {Γ : Context m} (w p a b q : Fin m)
    (hq : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 a b) q)) (hp : Derives Γ (atOne w p q)) :
    Derives Γ (implicationRead w p a b) := by
  apply Derives.exI q
  simpa only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, ProjectionTraceSyntax.args2_map,
    atOne_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hq hp

end PPAC.Migration.Internal.ProofMPSyntax
