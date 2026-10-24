import PPAC.Migration.Internal.ProjectBoundShiftSyntax

/-! Exact point laws and actual variable/successor uniqueness, in the original kernel. -/
namespace PPAC.Migration.Internal.ProjectBoundShiftPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectBoundShiftSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem code_input_subst {m} {Γ : Context m} (w i j x : Fin m) (he : Derives Γ (.equal i j))
    (hc : Derives Γ (SyntaxVariableSyntax.code true w i x)) : Derives Γ (SyntaxVariableSyntax.code true w j x) := by
  let P := SyntaxVariableSyntax.code true w.castSucc (Fin.last m) x.castSucc
  have h0 : P.instantiate i = SyntaxVariableSyntax.code true w i x := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate j = SyntaxVariableSyntax.code true w j x := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem successor_input_subst {m} {Γ : Context m} (s i j : Fin m) (he : Derives Γ (.equal i j))
    (hs : Derives Γ (successor s i)) : Derives Γ (successor s j) := by
  let P := successor s.castSucc (Fin.last m)
  have h0 : P.instantiate i = successor s i := by
    simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate j = successor s j := by
    simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem matrix_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y q i j u v : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (matrix w x y i j)) (hq : Derives Γ (matrix w x q u v)) :
    Derives Γ (.equal y q) := by
  have hi := SyntaxVariableDecode.index_eq hZ true w i u x hw (.conjL hy) (.conjL hq)
  have hs := successor_input_subst j i u hi (.conjL (.conjR hy))
  have hj := InsertLogic.unique j v u u (ZFContext.arithmetic hZ).base.extensionality hs (.conjL (.conjR hq))
  have hc := code_input_subst w j v y hj (.conjR (.conjR hy))
  exact SyntaxVariables.unique hZ true w v y q hw hc (.conjR (.conjR hq))

theorem matrix_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B f x y i j : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hB : Derives Γ (successor B b)) (hx : Derives Γ (SyntaxTermSyntax.branch true w b x))
    (hm : Derives Γ (matrix w x y i j)) : Derives Γ (SyntaxTermSyntax.term w B f y) := by
  have hi := SyntaxTermBranches.member hZ true w b x i hw (.conjL hm) hx
  have hiW := SyntaxVariableDecode.index_natural true w i x (.conjL hm)
  have hj := SyntaxIndexLiftOrder.successor_member hZ w i b j B hw hiW hb hi (.conjL (.conjR hm)) hB
  have hBW := OmegaStructureAlgebra.successor_member w B b (ZFContext.arithmetic hZ).base.extensionality hw hb hB
  exact SyntaxTermSyntax.intro_term true w B f y j (.conjI (.conjI hBW hf) hj) (.conjR (.conjR hm))

end PPAC.Migration.Internal.ProjectBoundShiftPoint
