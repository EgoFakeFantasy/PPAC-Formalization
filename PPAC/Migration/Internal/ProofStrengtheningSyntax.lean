import PPAC.Migration.Internal.OriginalTransformExprQuery
import PPAC.Migration.Internal.ProofProjectionExpr
import PPAC.Migration.Internal.OriginalWeakenFormulaRun
import PPAC.Migration.Internal.PureProofSubstitutionQueries

/-! 直接取原strengthening四查询；后继自由界是对象见证，绝不调用宿主eval。 -/
namespace PPAC.Migration.Internal.ProofStrengtheningSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def formulaQuery : Expr 4 := (ObjectProofNode.strengtheningShape.queries[0]).2
def freeQuery : Expr 4 := (ObjectProofNode.strengtheningShape.queries[1]).2
def predecessorFormulaQuery : Expr 4 := (ObjectProofNode.strengtheningShape.queries[2]).2
def transformQuery : Expr 4 := (ObjectProofNode.strengtheningShape.queries[3]).2

theorem actual_formula : ObjectProofNode.strengtheningShape.queries[0] = ObjectProofNode.formula (.var 0) (.var 1) := rfl
theorem actual_free : ObjectProofNode.strengtheningShape.queries[1] = ObjectProofNode.projection (.var 2) 0 (.succ (.var 0)) := rfl
theorem actual_predecessorFormula : ObjectProofNode.strengtheningShape.queries[2] = ObjectProofNode.projection (.var 2) 1 (.var 3) := rfl
theorem actual_transform : ObjectProofNode.strengtheningShape.queries[3] = ObjectProofNode.transform 0 (.literal 0) (.var 1) (.var 3) := rfl

def bundle {m} (w : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query formulaQuery w env).conj ((ProjectionExprQuery.query freeQuery w env).conj
    ((ProjectionExprQuery.query predecessorFormulaQuery w env).conj (OriginalTransformExprQuery.query transformQuery w env)))

def atSuccessor {m} (w z B : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) z (env 0)).conj ((RawCodeFieldSyntax.field w (env 2) z B).conj
    ((ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 3)).conj
      (WeakenFreeProgramSyntax.executed w z (env 0) B (env 1) (env 3))))

def specification {m} (w z : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((successor (Fin.last m) (env 0).castSucc).conj (atSuccessor w.castSucc z.castSucc (Fin.last m) (fun j => (env j).castSucc)))

theorem bundle_rename {m l} (w : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (bundle w env).rename ρ = bundle (ρ w) (fun j => ρ (env j)) := by
  simp only [bundle, Formula.rename, PureSyntaxExprQuery.query_rename, ProjectionExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem atSuccessor_rename {m l} (w z B : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (atSuccessor w z B env).rename ρ = atSuccessor (ρ w) (ρ z) (ρ B) (fun j => ρ (env j)) := by
  simp only [atSuccessor, Formula.rename, FormulaCodeSyntax.formulaCode_rename, RawCodeFieldSyntax.field_rename,
    ProofSubstitutionProjectionSyntax.atOne_rename, WeakenFreeProgramSyntax.executed_rename]

theorem specification_rename {m l} (w z : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (specification w z env).rename ρ = specification (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [specification, Formula.rename, successor_rename, atSuccessor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_specification {m} {Γ : Context m} (w z B : Fin m) (env : Fin 4 → Fin m)
    (hs : Derives Γ (successor B (env 0))) (ha : Derives Γ (atSuccessor w z B env)) : Derives Γ (specification w z env) := by
  apply Derives.exI B
  simpa only [specification, Formula.instantiate, Formula.rename, successor_rename, atSuccessor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs ha

end PPAC.Migration.Internal.ProofStrengtheningSyntax
