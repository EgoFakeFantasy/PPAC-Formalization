import PPAC.Migration.Internal.ProjectCompilerCompleteConstructors

/-! Actual output-existence checks retain the original strict child guard and successor scope. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteQuerySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCaseSyntax ProjectCompilerRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

def someCheck {m} (advance : Bool) (w n x b : Fin m) : Formula m := .ex
  (check advance codeMatrix (parameters w.castSucc) n.castSucc x.castSucc b.castSucc (Fin.last m))

theorem someCheck_rename {m j} (advance : Bool) (w n x b : Fin m) (σ : Fin m → Fin j) :
    (someCheck advance w n x b).rename σ = someCheck advance (σ w) (σ n) (σ x) (σ b) := by
  simp only [someCheck, Formula.rename, check_rename, parameters_map, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_someCheck {m} {Γ : Context m} (advance : Bool) (w n x b q : Fin m)
    (hc : Derives Γ (check advance codeMatrix (parameters w) n x b q)) : Derives Γ (someCheck advance w n x b) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, check_rename, parameters_map,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc

theorem query_of_output {m} {Γ : Context m} (w n x b q : Fin m) (hx : Derives Γ (.mem x n))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w x b q)) :
    Derives Γ (queried codeMatrix (parameters w) n x b q) :=
  of_eq (by simp only [queried, codeMatrix_at, parameters]) (Derives.conjI hx hc)

theorem intro_advanced {m} {Γ : Context m} (w n x b q B : Fin m) (hs : Derives Γ (successor B b))
    (hc : Derives Γ (queried codeMatrix (parameters w) n x B q)) :
    Derives Γ (advanced codeMatrix (parameters w) n x b q) := by
  apply Derives.exI B
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, queried_rename, parameters_map,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI hs hc)

end PPAC.Migration.Internal.ProjectCompilerCompleteQuerySyntax
