import PPAC.Migration.Internal.ProofTreeTraceSyntax

/-! 带实际局部检查的原12规则对轨迹成员单调；局部检查与轨迹参数独立。 -/
namespace PPAC.Migration.Internal.ProofTreeTraceMonotone
open Source SourceAlgebra SourceLogic ProofTreeTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem step {m} {Γ : Context m} (test : Formula 1) (w r R S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (ProofTreeTraceSyntax.step test w r R)) :
    Derives Γ (ProofTreeTraceSyntax.step test w r S) :=
  .conjI (HornTraceMonotone.step _ w r R S hs (.conjL he)) (.conjR he)

theorem row_subst {m} {Γ : Context m} (test : Formula 1) (w r s R : Fin m) (he : Derives Γ (.equal r s))
    (hr : Derives Γ (ProofTreeTraceSyntax.step test w r R)) : Derives Γ (ProofTreeTraceSyntax.step test w s R) := by
  let P := ProofTreeTraceSyntax.step test w.castSucc (Fin.last m) R.castSucc
  have h0 : P.instantiate r = ProofTreeTraceSyntax.step test w r R := by
    simp only [P, Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate s = ProofTreeTraceSyntax.step test w s R := by
    simp only [P, Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

end PPAC.Migration.Internal.ProofTreeTraceMonotone
