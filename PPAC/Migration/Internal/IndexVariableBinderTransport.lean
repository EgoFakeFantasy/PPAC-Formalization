import PPAC.Migration.Internal.IndexVariableBinderReading

/-! 全部字段读取装配为提升后两份原变量像图；规范头部和位移图在对象存在量词内消去。 -/
namespace PPAC.Migration.Internal.IndexVariableBinderTransport
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem ready_mapped {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d A C L K H U V z n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxVariableImageSyntax.mapped true w r a c d f))
    (hg : Derives Γ (SyntaxVariableImageSyntax.mapped false w s b c d g))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C L))
    (hn : Derives Γ (SyntaxMixedImageBinderSyntax.ready w f g a b c d A C K H U V z n)) :
    Derives Γ ((SyntaxVariableImageSyntax.mapped true w L A C d K).conj (SyntaxVariableImageSyntax.mapped false w s b C d H)) := by
  have hMaps := SyntaxMixedImageLiftFields.target_maps w U V f g a b c d A C n K H (.conjR (.conjR (.conjR hn)))
  have hCtx : Derives Γ (SyntaxTermSyntax.contexts w C d) := .conjL (.conjR (.conjL hMaps))
  have hIndex : Derives Γ (SyntaxIndexMapSyntax.indexMap w L A C) := .conjL (.conjR (.conjR (.conjR hl)))
  have hBound := IndexVariableBinderReading.bound_reads hZ w r f g a b c d A C L K H U V z n hw hf hl hn
  have hFree := IndexVariableBinderReading.free_reads hZ w s f g a b c d A C K H U V z n hw hg hn
  exact .conjI (IndexVariableImageReading.mapped_from_reads hZ true w L A C d K (.conjI hCtx hIndex) (.conjL hMaps) hBound)
    (IndexVariableImageReading.mapped_from_reads hZ false w s b C d H (.conjI hCtx (.conjR (.conjL hg))) (.conjR hMaps) hFree)

theorem mapped_after_binder {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d A C L K H : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SyntaxVariableImageSyntax.mapped true w r a c d f))
    (hg : Derives Γ (SyntaxVariableImageSyntax.mapped false w s b c d g))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C L))
    (hn : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w f g a b c d A C K H)) :
    Derives Γ ((SyntaxVariableImageSyntax.mapped true w L A C d K).conj (SyntaxVariableImageSyntax.mapped false w s b C d H)) := by
  let B := SyntaxMixedImageBinderSyntax.body w f g a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hn
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hf4 : Derives Δ (SyntaxVariableImageSyntax.mapped true w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableImageSyntax.mapped_rename]) (SyntaxRenameBinders.under_4 hf B)
  have hg4 : Derives Δ (SyntaxVariableImageSyntax.mapped false w.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableImageSyntax.mapped_rename]) (SyntaxRenameBinders.under_4 hg B)
  have hl4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (SyntaxRenameBinders.under_4 hl B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := ready_mapped hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hf4 hg4 hl4 hB
  exact of_eq (by simp only [Formula.raise, Formula.rename, SyntaxVariableImageSyntax.mapped_rename]) ho

end PPAC.Migration.Internal.IndexVariableBinderTransport
