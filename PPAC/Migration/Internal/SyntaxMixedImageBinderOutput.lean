import PPAC.Migration.Internal.SyntaxMixedImageBinderAlign

/-! 全内部混合binder的实际输出、准确类型及独立于全部规范见证的两表唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageBinderOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d))
    (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (existsPair w r s a b c d A C) := by
  let B := SyntaxMixedImageLiftState.snapshot w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have he : Derives Γ (.ex (.ex (.ex (.ex B)))) := SyntaxMixedImageLiftState.exists_state hZ w r s a b c d A C hw hi hA hC
  apply SyntaxRenameBinders.eliminate_4 B _ he
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  let Q := SyntaxMixedImageLiftSyntax.lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5))
  let Δ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Ξ))
  have hp : Derives Ξ (.ex (.ex Q)) := .conjR (.conjR (.conjR hB))
  apply SyntaxRenameBinders.eliminate_2 Q _ hp
  have hb6 : Derives Δ (SyntaxMixedImageLiftState.snapshot w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc) :=
    of_eq (by simp only [B, Formula.raise, SyntaxMixedImageLiftState.snapshot_rename]) (SyntaxRenameBinders.under_2 hB Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hr : Derives Δ (ready w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc) :=
    .conjI (.conjL hb6) (.conjI (.conjL (.conjR hb6)) (.conjI (.conjL (.conjR (.conjR hb6))) hQ))
  have hl := intro_lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc hr
  have ho := intro_pair w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) hl
  exact of_eq (by simp only [Formula.raise, existsPair_rename]) ho

theorem at_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h R S z n : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d S)) (hHead : Derives Γ (SyntaxMixedImageHead.head w C d z n))
    (hl : Derives Γ (lifted w r s a b c d A C k h)) :
    Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) := by
  let B := body w r s a b c d A C k h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hr4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_4 hR B)
  have hs4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (SyntaxRenameBinders.under_4 hS B)
  have hh4 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageHead.head_rename]) (SyntaxRenameBinders.under_4 hHead B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageBinderAlign.align hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hr4 hs4 hh4 hB
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageLiftSyntax.lifted_rename]) ho

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h K H : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w r s a b c d A C k h))
    (hL : Derives Γ (lifted w r s a b c d A C K H)) : Derives Γ ((Formula.equal k K).conj (Formula.equal h H)) := by
  let B := body w r s a b c d A C k h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hL4 : Derives Δ (lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_4 hL B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv := at_witnesses hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 (.conjL hB) (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) hL4
  exact SyntaxMixedImageLiftUnique.unique_pair hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR hB))) hv

theorem target_maps {m} {Γ : Context m} (w r s a b c d A C k h : Fin m)
    (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ (SyntaxTermImageSyntax.maps w k h A b C d) := by
  let B := body w r s a b c d A C k h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageLiftFields.target_maps w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) ho

end PPAC.Migration.Internal.SyntaxMixedImageBinderOutput
