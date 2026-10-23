import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentTyping

/-! 原数值首槽环境码对的实际唯一性，独立于隐藏实际图与内部头码见证。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopCodedEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_at_states {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S U V f g F G : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (instantiateState w a b A t R S f g))
    (h2 : Derives Γ (instantiateState w a b A t U V F G)) : Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  have he := SyntaxTopEnvironmentUnique.instantiate_unique hZ w a b A t f g F G (.conjL h1) (.conjL h2)
  have hf := SyntaxMixedImageCodeUnique.subst_graph w F A a b U f (eq_symm (.conjL he)) (.conjL (.conjR h2))
  have hg := SyntaxMixedImageCodeUnique.subst_graph w G b a b V g (eq_symm (.conjR he)) (.conjR (.conjR h2))
  exact SyntaxMixedImageCodePairs.codes_unique hZ w f g A b a b R S U V hw (.conjR h1) (.conjI hf hg)

theorem instantiate_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t R S U V : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (instantiateCoded w a b A t R S))
    (h2 : Derives Γ (instantiateCoded w a b A t U V)) : Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  let E := instantiateBody w a b A t R S
  let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ h1
  have h2k : Derives Ξ (instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, instantiateCoded_rename]) (SyntaxRenameBinders.under_2 h2 E)
  let H := instantiateBody w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply SyntaxRenameBinders.eliminate_2 H _ h2k
  have hZ4 := SyntaxRenameBinders.zf_under_2 (SyntaxRenameBinders.zf_under_2 hZ E) H
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hw E) H)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have he4 : Derives Δ (instantiateState w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [E, instantiateBody, Formula.raise, instantiateState_rename]) (SyntaxRenameBinders.under_2 hE H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact instantiate_at_states hZ4 w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 he4 hH

theorem abstract_at_states {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S U V f g F G : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (abstractState w a b A B R S f g))
    (h2 : Derives Γ (abstractState w a b A B U V F G)) : Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  have he := SyntaxTopEnvironmentUnique.abstract_unique hZ w a b A B f g F G hw (.conjL h1) (.conjL h2)
  have hf := SyntaxMixedImageCodeUnique.subst_graph w F a A b U f (eq_symm (.conjL he)) (.conjL (.conjR h2))
  have hg := SyntaxMixedImageCodeUnique.subst_graph w G B A b V g (eq_symm (.conjR he)) (.conjR (.conjR h2))
  exact SyntaxMixedImageCodePairs.codes_unique hZ w f g a B A b R S U V hw (.conjR h1) (.conjI hf hg)

theorem abstract_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B R S U V : Fin m)
    (hw : Derives Γ (omega w)) (h1 : Derives Γ (abstractCoded w a b A B R S))
    (h2 : Derives Γ (abstractCoded w a b A B U V)) : Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  let E := abstractBody w a b A B R S
  let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ h1
  have h2k : Derives Ξ (abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, abstractCoded_rename]) (SyntaxRenameBinders.under_2 h2 E)
  let H := abstractBody w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply SyntaxRenameBinders.eliminate_2 H _ h2k
  have hZ4 := SyntaxRenameBinders.zf_under_2 (SyntaxRenameBinders.zf_under_2 hZ E) H
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hw E) H)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have he4 : Derives Δ (abstractState w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [E, abstractBody, Formula.raise, abstractState_rename]) (SyntaxRenameBinders.under_2 hE H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact abstract_at_states hZ4 w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc V.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 he4 hH

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentUnique
