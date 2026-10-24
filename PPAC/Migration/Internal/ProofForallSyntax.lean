import PPAC.Migration.Internal.OriginalTransformExprQuery
import PPAC.Migration.Internal.ProofProjectionExpr
import PPAC.Migration.Internal.AbstractTopFormulaOperation
import PPAC.Migration.Internal.PureProofSubstitutionQueries

/-! 原forall四查询与实际AbstractFreeTop规格；两个后继界均为内部对象见证。 -/
namespace PPAC.Migration.Internal.ProofForallSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def formulaQuery : Expr 4 := (ObjectProofNode.forallShape.queries[0]).2
def freeQuery : Expr 4 := (ObjectProofNode.forallShape.queries[1]).2
def predecessorFormulaQuery : Expr 4 := (ObjectProofNode.forallShape.queries[2]).2
def transformQuery : Expr 4 := (ObjectProofNode.forallShape.queries[3]).2

theorem actual_formula : ObjectProofNode.forallShape.queries[0] = ObjectProofNode.formula (.succ (.var 0)) (.var 3) := rfl
theorem actual_free : ObjectProofNode.forallShape.queries[1] = ObjectProofNode.projection (.var 2) 0 (.succ (.var 0)) := rfl
theorem actual_predecessorFormula : ObjectProofNode.forallShape.queries[2] = ObjectProofNode.projection (.var 2) 1 (.var 3) := rfl
theorem actual_transform : ObjectProofNode.forallShape.queries[3] = ObjectProofNode.transform 1 (.literal 0) (.var 3) (.var 1) := rfl

def bundle {m} (w : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query formulaQuery w env).conj ((ProjectionExprQuery.query freeQuery w env).conj
    ((ProjectionExprQuery.query predecessorFormulaQuery w env).conj (OriginalTransformExprQuery.query transformQuery w env)))

def atSuccessor {m} (w z A B : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 3) z B).conj ((RawCodeFieldSyntax.field w (env 2) z B).conj
    ((ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 3)).conj
      (SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 3) (env 1))))

def atOneSpecification {m} (w z A : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) (env 0).castSucc).conj (atSuccessor w.castSucc z.castSucc A.castSucc (Fin.last m) (fun j => (env j).castSucc)))

theorem bundle_rename {m l} (w : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (bundle w env).rename ρ = bundle (ρ w) (fun j => ρ (env j)) := by
  simp only [bundle, Formula.rename, PureSyntaxExprQuery.query_rename, ProjectionExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atSuccessor_rename {m l} (w z A B : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atSuccessor w z A B env).rename ρ = atSuccessor (ρ w) (ρ z) (ρ A) (ρ B) (fun j => ρ (env j)) := by
  simp only [atSuccessor, Formula.rename, FormulaCodeSyntax.formulaCode_rename, RawCodeFieldSyntax.field_rename,
    ProofSubstitutionProjectionSyntax.atOne_rename, SyntaxTopFormulaSyntax.abstracted_rename]

theorem atOneSpecification_rename {m l} (w z A : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atOneSpecification w z A env).rename ρ = atOneSpecification (ρ w) (ρ z) (ρ A) (fun j => ρ (env j)) := by
  simp only [atOneSpecification, Formula.rename, successor_rename, atSuccessor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_atOneSpecification {m} {Γ : Context m} (w z A B : Fin m) (env : Fin 4 → Fin m)
    (hs : Derives Γ (successor B (env 0))) (ha : Derives Γ (atSuccessor w z A B env)) : Derives Γ (atOneSpecification w z A env) := by
  apply Derives.exI B
  simpa only [atOneSpecification, Formula.instantiate, Formula.rename, successor_rename, atSuccessor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

def specification {m} (w z : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) z.castSucc).conj (atOneSpecification w.castSucc z.castSucc (Fin.last m) (fun j => (env j).castSucc)))

theorem specification_rename {m l} (w z : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (specification w z env).rename ρ = specification (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [specification, Formula.rename, successor_rename, atOneSpecification_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_specification {m} {Γ : Context m} (w z A : Fin m) (env : Fin 4 → Fin m)
    (hs : Derives Γ (successor A z)) (ha : Derives Γ (atOneSpecification w z A env)) : Derives Γ (specification w z env) := by
  apply Derives.exI A
  simpa only [specification, Formula.instantiate, Formula.rename, successor_rename, atOneSpecification_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

end PPAC.Migration.Internal.ProofForallSyntax
