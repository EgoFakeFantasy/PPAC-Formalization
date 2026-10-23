import PPAC.Migration.Internal.SyntaxCodedMixedBinderExistence

/-! 数值码binder输出不依赖四张实际图的解码见证；原图和原列表码唯一性在对象核内接合。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_states {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V r s k h u v f g : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (state w R S a b c d A C K H r s k h))
    (hB : Derives Γ (state w R S a b c d A C U V u v f g)) : Derives Γ ((Formula.equal K U).conj (Formula.equal H V)) := by
  have ei := SyntaxMixedImageCodePairs.graphs_unique hZ w u v a b c d R S r s (.conjL hB) (.conjL hb)
  have hr := SyntaxCodedMixedBinderGraphs.subst_bound_source w u v a b c d A C f g r (.conjL ei) (.conjL (.conjR hB))
  have hs := SyntaxCodedMixedBinderGraphs.subst_free_source w r v a b c d A C f g s (.conjR ei) hr
  have eo := SyntaxMixedImageBinderOutput.unique_pair hZ w r s a b c d A C k h f g hw (.conjL (.conjR hb)) hs
  have ek := SyntaxMixedImageCodeUnique.subst_graph w f A C d U k (eq_symm (.conjL eo)) (.conjL (.conjR (.conjR hB)))
  have eh := SyntaxMixedImageCodeUnique.subst_graph w g b C d V h (eq_symm (.conjR eo)) (.conjR (.conjR (.conjR hB)))
  exact SyntaxMixedImageCodePairs.codes_unique hZ w k h A b C d K H U V hw (.conjR (.conjR hb)) (.conjI ek eh)

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H U V : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w R S a b c d A C K H))
    (hL : Derives Γ (lifted w R S a b c d A C U V)) : Derives Γ ((Formula.equal K U).conj (Formula.equal H V)) := by
  let B := body w R S a b c d A C K H
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
  have hL4 : Derives Ξ (lifted w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_4 hL B)
  let D := body w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Ξ))))
  apply SyntaxRenameBinders.eliminate_4 D _ hL4
  have hZ8 := SyntaxRenameBinders.zf_under_4 hZ4 D
  have hw8 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw4 D)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb8 : Derives Δ (state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [B, body, Formula.raise, state_rename]) (SyntaxRenameBinders.under_4 hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact from_states hZ8 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+7)) hw8 hb8 hD

end PPAC.Migration.Internal.SyntaxCodedMixedBinderUnique
