import PPAC.Migration.Internal.ProjectionExprQueryTyping
import YesMetaZFC.Automation.ObjectProofNode

/-! 直接取原替换节点第2／3项投影；独立接受定义不引用元数据规格。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionProjectionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def freeProjection : Expr 6 := (ObjectProofNode.substitutionShape.queries[2]).2
def formulaProjection : Expr 6 := (ObjectProofNode.substitutionShape.queries[3]).2

def freeFields : Fin 3 → Expr 6 := ProjectionTracePremises.three (.var 4) (.literal 0) (.var 2)
def formulaFields : Fin 3 → Expr 6 := ProjectionTracePremises.three (.var 4) (.literal 1) (.var 5)

theorem actual_free : ObjectProofNode.substitutionShape.queries[2] = ObjectProofNode.projection (.var 4) 0 (.var 2) := rfl
theorem actual_formula : ObjectProofNode.substitutionShape.queries[3] = ObjectProofNode.projection (.var 4) 1 (.var 5) := rfl
theorem free_expr : freeProjection = Expr.node (.literal 2) (List.ofFn freeFields) := rfl
theorem formula_expr : formulaProjection = Expr.node (.literal 2) (List.ofFn formulaFields) := rfl

def atOne {m} (w p y : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 1 (Fin.last m)).conj (RawCodeFieldSyntax.field w.castSucc p.castSucc (Fin.last m) y.castSucc))

def projections {m} (w : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (ProjectionExprQuery.query freeProjection w env).conj (ProjectionExprQuery.query formulaProjection w env)

def metadata {m} (w z : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (RawCodeFieldSyntax.field w (env 4) z (env 2)).conj (atOne w (env 4) (env 5))

theorem atOne_rename {m l} (w p y : Fin m) (ρ : Fin m → Fin l) :
    (atOne w p y).rename ρ = atOne (ρ w) (ρ p) (ρ y) := by
  simp only [atOne, Formula.rename, SyntaxNumeralSyntax.numeral_rename, RawCodeFieldSyntax.field_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem projections_rename {m l} (w : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (projections w env).rename ρ = projections (ρ w) (fun j => ρ (env j)) := by
  simp only [projections, Formula.rename, ProjectionExprQuery.query_rename]

theorem metadata_rename {m l} (w z : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (metadata w z env).rename ρ = metadata (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [metadata, Formula.rename, RawCodeFieldSyntax.field_rename, atOne_rename]

theorem intro_atOne {m} {Γ : Context m} (w p y one : Fin m)
    (ho : Derives Γ (SyntaxNumeralSyntax.numeral 1 one)) (hf : Derives Γ (RawCodeFieldSyntax.field w p one y)) :
    Derives Γ (atOne w p y) := by
  apply Derives.exI one
  simpa only [Formula.instantiate, Formula.rename, SyntaxNumeralSyntax.numeral_rename, RawCodeFieldSyntax.field_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI ho hf

end PPAC.Migration.Internal.ProofSubstitutionProjectionSyntax
