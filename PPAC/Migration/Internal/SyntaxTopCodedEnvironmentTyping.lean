import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentExistence

/-! 原数值首槽环境的准确输入、完整项列表类型和自然码守卫。 -/
namespace PPAC.Migration.Internal.SyntaxTopCodedEnvironmentTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopCodedEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_input {m} {Γ : Context m} (w a b A t R S : Fin m)
    (hc : Derives Γ (instantiateCoded w a b A t R S)) : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := by
  let E := instantiateBody w a b A t R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := SyntaxTopEnvironmentTyping.instantiate_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hE)
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.instantiateInput_rename]) ho

theorem instantiate_lists {m} {Γ : Context m} (w a b A t R S : Fin m)
    (hc : Derives Γ (instantiateCoded w a b A t R S)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w A b a b R S) := by
  let E := instantiateBody w a b A t R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (.conjR hE)
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) ho

theorem instantiate_natural {m} {Γ : Context m} (w a b A t R S : Fin m)
    (hc : Derives Γ (instantiateCoded w a b A t R S)) : Derives Γ ((Formula.mem R w).conj (.mem S w)) := by
  have ht := instantiate_lists w a b A t R S hc
  exact .conjI (.conjL (.conjL (.conjR (.conjR (.conjL ht))))) (.conjL (.conjL (.conjR (.conjR (.conjR ht)))))

theorem abstract_input {m} {Γ : Context m} (w a b A B R S : Fin m)
    (hc : Derives Γ (abstractCoded w a b A B R S)) : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := by
  let E := abstractBody w a b A B R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := SyntaxTopEnvironmentTyping.abstract_input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hE)
  exact of_eq (by simp only [Formula.raise, SyntaxTopEnvironmentSyntax.abstractInput_rename]) ho

theorem abstract_lists {m} {Γ : Context m} (w a b A B R S : Fin m)
    (hc : Derives Γ (abstractCoded w a b A B R S)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a B A b R S) := by
  let E := abstractBody w a b A B R S
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (.conjR hE)
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) ho

theorem abstract_natural {m} {Γ : Context m} (w a b A B R S : Fin m)
    (hc : Derives Γ (abstractCoded w a b A B R S)) : Derives Γ ((Formula.mem R w).conj (.mem S w)) := by
  have ht := abstract_lists w a b A B R S hc
  exact .conjI (.conjL (.conjL (.conjR (.conjR (.conjL ht))))) (.conjL (.conjL (.conjR (.conjR (.conjR ht)))))

end PPAC.Migration.Internal.SyntaxTopCodedEnvironmentTyping
