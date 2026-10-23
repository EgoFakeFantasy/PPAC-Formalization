import PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentTyping

/-! 不同实际后继范围及两个输出码的全内部binder见证唯一；用于混合量词子判断对齐。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaBinderAlign
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_source_bound_size {m} {Γ : Context m} (w r s a b c d A C K H V : Fin m)
    (he : Derives Γ (.equal A V)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H)) :
    Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d V C K H) := by
  let P := SyntaxCodedMixedBinderSyntax.lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) C.castSucc K.castSucc H.castSucc
  have e0 : P.instantiate A = SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxCodedMixedBinderSyntax.lifted w r s a b c d V C K H := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_target_bound_size {m} {Γ : Context m} (w r s a b c d A C K H V : Fin m)
    (he : Derives Γ (.equal C V)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H)) :
    Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A V K H) := by
  let P := SyntaxCodedMixedBinderSyntax.lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc (Fin.last m) K.castSucc H.castSucc
  have e0 : P.instantiate C = SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A V K H := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem all_targets_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C K H U V L M : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (hR : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d U V L M)) :
    Derives Γ ((Formula.equal A U).conj ((Formula.equal C V).conj ((Formula.equal K L).conj (Formula.equal H M)))) := by
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted w r s a b c d A C K H hL
  have hj := SyntaxCodedMixedBinderTyping.input_of_lifted w r s a b c d U V L M hR
  have eA := OmegaUniversal.successor_unique A U a (ZFContext.arithmetic hZ).base.extensionality (.conjL (.conjR hi)) (.conjL (.conjR hj))
  have eC := OmegaUniversal.successor_unique C V c (ZFContext.arithmetic hZ).base.extensionality (.conjR (.conjR hi)) (.conjR (.conjR hj))
  have hA := subst_source_bound_size w r s a b c d A C K H U eA hL
  have hC := subst_target_bound_size w r s a b c d U C K H V eC hA
  have ep := SyntaxCodedMixedBinderUnique.unique_pair hZ w r s a b c d U V K H L M hw hC hR
  exact .conjI eA (.conjI eC ep)

end PPAC.Migration.Internal.SyntaxMixedFormulaBinderAlign
