import PPAC.Migration.Internal.SyntaxMixedImageBinderSyntax

/-! 规范binder见证在对象层唯一并可对齐；不把存在见证抽取为Lean函数。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageBinderAlign
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem head_code_subst_index {m} {Γ : Context m} (w z Z n : Fin m)
    (he : Derives Γ (.equal z Z)) (hc : Derives Γ (SyntaxVariableSyntax.code true w z n)) :
    Derives Γ (SyntaxVariableSyntax.code true w Z n) := by
  let P := SyntaxVariableSyntax.code true w.castSucc (Fin.last m) n.castSucc
  have e0 : P.instantiate z = SyntaxVariableSyntax.code true w z n := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate Z = SyntaxVariableSyntax.code true w Z n := by
    simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hc))

theorem head_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C d z n Z N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hH : Derives Γ (SyntaxMixedImageHead.head w C d Z N)) : Derives Γ ((Formula.equal z Z).conj (Formula.equal n N)) := by
  have ez := OmegaUniversal.empty_unique z Z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) (.conjL hH)
  have hc := head_code_subst_index w z Z n ez (.conjL (.conjR hh))
  exact .conjI ez (SyntaxVariables.unique hZ true w Z n N hw hc (.conjL (.conjR hH)))

theorem subst_bound_map {m} {Γ : Context m} (w R S r s a b c d A C n k h V : Fin m)
    (he : Derives Γ (.equal R V)) (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h)) :
    Derives Γ (SyntaxMixedImageLiftSyntax.lifted w V S r s a b c d A C n k h) := by
  let P := SyntaxMixedImageLiftSyntax.lifted w.castSucc (Fin.last m) S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc
  have e0 : P.instantiate R = SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageLiftSyntax.lifted w V S r s a b c d A C n k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_free_map {m} {Γ : Context m} (w R S r s a b c d A C n k h V : Fin m)
    (he : Derives Γ (.equal S V)) (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h)) :
    Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R V r s a b c d A C n k h) := by
  let P := SyntaxMixedImageLiftSyntax.lifted w.castSucc R.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc h.castSucc
  have e0 : P.instantiate S = SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageLiftSyntax.lifted w R V r s a b c d A C n k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_head_code {m} {Γ : Context m} (w R S r s a b c d A C n k h V : Fin m)
    (he : Derives Γ (.equal n V)) (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h)) :
    Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C V k h) := by
  let P := SyntaxMixedImageLiftSyntax.lifted w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m) k.castSucc h.castSucc
  have e0 : P.instantiate n = SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C V k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem align {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h R S z n U V Z N : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d S)) (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hq : Derives Γ (SyntaxMixedImageBinderSyntax.ready w r s a b c d A C k h U V Z N)) :
    Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) := by
  have er := SyntaxFreeShiftGraph.unique_map hZ w c C U R (.conjL hq) hR
  have es := SyntaxIdentityUnique.map_unique hZ w d V S (.conjL (.conjR hq)) hS
  have en := head_unique hZ w C d Z N z n hw (.conjL (.conjR (.conjR hq))) hHead
  have hr := subst_bound_map w U V r s a b c d A C N k h R er (.conjR (.conjR (.conjR hq)))
  have hs := subst_free_map w R V r s a b c d A C N k h S es hr
  exact subst_head_code w R S r s a b c d A C N k h n (.conjR en) hs

end PPAC.Migration.Internal.SyntaxMixedImageBinderAlign
