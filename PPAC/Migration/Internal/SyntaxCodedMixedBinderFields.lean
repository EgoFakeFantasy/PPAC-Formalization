import PPAC.Migration.Internal.SyntaxCodedMixedBinderFiber

/-! 完整数值环境binder的原列表字段律：新零、旧bound后继、旧free保持，所有项像bound分量均移动。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V z n q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n)) :
    Derives Γ (((Formula.mem z A).conj (StructuralListFieldSyntax.field w K z q)).iff (Formula.equal q n)) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hu4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_4 hU B)
  have hv4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_4 hV B)
  have hh4 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_4 hHead B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := SyntaxMixedImageBinderFields.zero_iff hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 hu4 hv4 hh4 (.conjL (.conjR hB))
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR (.conjR hB)))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename]) ho

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V z n i j t q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hj : Derives Γ (.mem j a)) (hi : Derives Γ (successor i j)) (ht : Derives Γ (StructuralListFieldSyntax.field w R j t)) :
    Derives Γ (((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff (SyntaxRenameTermSyntax.renamed w U V c d C d t q)) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hu4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_4 hU B)
  have hv4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_4 hV B)
  have hh4 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_4 hHead B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hj4 : Derives Δ (.mem j.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc) := SyntaxRenameBinders.under_4 hj B
  have ht4 : Derives Δ (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListFieldSyntax.field_rename]) (SyntaxRenameBinders.under_4 ht B)
  have hs := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc (.conjL (.conjL hB))
  have he := Derives.impE (.conjR hs) (.conjI hj4 ht4)
  have hi4 : Derives Δ (successor i.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_4 hi B)
  have ha := SyntaxMixedImageBinderFields.bound_iff hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 hu4 hv4 hh4 (.conjL (.conjR hB)) hj4 hi4 he
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR (.conjR hB)))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V z n j t q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w R S a b c d A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n)) (hj : Derives Γ (.mem j b)) (ht : Derives Γ (StructuralListFieldSyntax.field w S j t)) :
    Derives Γ (((Formula.mem j b).conj (StructuralListFieldSyntax.field w H j q)).iff (SyntaxRenameTermSyntax.renamed w U V c d C d t q)) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hu4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_4 hU B)
  have hv4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_4 hV B)
  have hh4 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_4 hHead B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hj4 : Derives Δ (.mem j.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc) := SyntaxRenameBinders.under_4 hj B
  have ht4 : Derives Δ (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListFieldSyntax.field_rename]) (SyntaxRenameBinders.under_4 ht B)
  have hs := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc (.conjR (.conjL hB))
  have he := Derives.impE (.conjR hs) (.conjI hj4 ht4)
  have ha := SyntaxMixedImageBinderFields.free_iff hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 hu4 hv4 hh4 (.conjL (.conjR hB)) he
  have hc := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR hB)))
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) ha
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

end PPAC.Migration.Internal.SyntaxCodedMixedBinderFields
