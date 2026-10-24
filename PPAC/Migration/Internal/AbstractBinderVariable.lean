import PPAC.Migration.Internal.AbstractBinderVariablePoint

/-! 原mode1变量值在真实binder提升下的全候选协变；旧值的四分支及后继见证均实际消去。 -/
namespace PPAC.Migration.Internal.AbstractBinderVariable
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D I U V c e C x X t q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w))
    (hD : Derives Γ (successor D d)) (hI : Derives Γ (successor I i))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hX : Derives Γ (SyntaxVariableSyntax.code true w I X))
    (hv : Derives Γ (boundValue w d i x t)) :
    Derives Γ ((boundValue w D I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  apply Derives.disjE hv
  · let E := (Formula.mem i d).conj (.equal t x)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hcode := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal (ZFContext.add hZ E) true w i x t (add hw E) (add hx E))) (.conjR hE)
    exact AbstractBinderVariablePoint.preserved (ZFContext.add hZ E) w d i D I U V c e C X t q
      (add hw E) (add hd E) (add hD E) (add hI E) (.conjL hE) (add hU E) (add hV E) (add ht E) hcode (add hX E)
  · let E := boundShifted w d i t
    let B := (successor (Fin.last m) i.castSucc).conj ((Formula.mem d.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) t.castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under (add hd E) B
    have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under (add (SyntaxVariableDecode.index_natural true w i x hx) E) B
    have hD1 := of_eq (successor_rename D d Fin.castSucc) (under (add hD E) B)
    have hI1 := of_eq (successor_rename I i Fin.castSucc) (under (add hI E) B)
    have hU1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under (add hU E) B)
    have hV1 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under (add hV E) B)
    have ht1 := of_eq (SyntaxTermSyntax.term_rename w c e t Fin.castSucc) (under (add ht E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := OmegaUniversal.successor_unique (Fin.last m) I.castSucc i.castSucc (ZFContext.arithmetic hZ1).base.extensionality (.conjL hB) hI1
    have ha := UnorderedPairLogic.mem_container_subst (Fin.last m) I.castSucc d.castSucc he (.conjL (.conjR hB))
    have hc := AbstractVariableIndex.code_index_subst true w.castSucc (Fin.last m) I.castSucc t.castSucc he (.conjR (.conjR hB))
    have ho := AbstractBinderVariablePoint.shifted hZ1 w.castSucc d.castSucc i.castSucc D.castSucc I.castSucc U.castSucc V.castSucc c.castSucc e.castSucc C.castSucc X.castSucc t.castSucc q.castSucc hw1 hd1 hi1 hD1 hI1 ha hU1 hV1 ht1 hc
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, boundValue_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d i D U V c e C t q : Fin m)
    (hw : Derives Γ (omega w)) (hD : Derives Γ (successor D d))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (ht : Derives Γ (SyntaxTermSyntax.term w c e t)) (hv : Derives Γ (freeValue w d i t)) :
    Derives Γ ((freeValue w D i q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)) := by
  apply Derives.disjE hv
  · let E := (empty i).conj (SyntaxVariableSyntax.code true w d t)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact AbstractBinderVariablePoint.free_zero (ZFContext.add hZ E) w d i D U V c e C t q
      (add hw E) (add hD E) (.conjL hE) (add hU E) (add hV E) (add ht E) (.conjR hE)
  · let E := freeTail w i t
    let B := (successor i.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) t.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hU1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under (add hU E) B)
    have hV1 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under (add hV E) B)
    have ht1 := of_eq (SyntaxTermSyntax.term_rename w c e t Fin.castSucc) (under (add ht E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := AbstractBinderVariablePoint.free_successor hZ1 w.castSucc i.castSucc (Fin.last m) D.castSucc U.castSucc V.castSucc c.castSucc e.castSucc C.castSucc t.castSucc q.castSucc hw1 (.conjL hB) hU1 hV1 ht1 (.conjR hB)
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, freeValue_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

end PPAC.Migration.Internal.AbstractBinderVariable
