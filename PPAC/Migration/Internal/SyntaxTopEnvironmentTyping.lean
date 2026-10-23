import PPAC.Migration.Internal.SyntaxTopAbstractExistence

/-! 首槽环境的完整实际项像类型与准确合法输入；不预设未来公式操作。 -/
namespace PPAC.Migration.Internal.SyntaxTopEnvironmentTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopEnvironmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_data_maps {m} {Γ : Context m} (w a b A t f g u : Fin m)
    (hi : Derives Γ (instantiateData w a b A t f g u)) :
    Derives Γ (SyntaxTermImageSyntax.maps w f g A b a b) := by
  have hp := Derives.conjL (.conjR hi)
  exact .conjI (.conjL (.conjR (.conjR (.conjR hp))))
    (SyntaxVariableTableUnique.identity_type false w a b g (.conjR (.conjR hi)))

theorem abstract_data_maps {m} {Γ : Context m} (w a b A B f g u z n : Fin m)
    (hi : Derives Γ (abstractData w a b A B f g u z n)) :
    Derives Γ (SyntaxTermImageSyntax.maps w f g a B A b) := by
  have hp := Derives.conjR (.conjR (.conjR hi))
  exact .conjI (SyntaxVariableTableUnique.shifted_type true w a A b f (.conjL hi))
    (.conjL (.conjR (.conjR (.conjR hp))))

theorem instantiate_data_input {m} {Γ : Context m} (w a b A t f g u : Fin m)
    (hi : Derives Γ (instantiateData w a b A t f g u)) : Derives Γ (instantiateInput w a b A t) := by
  have hp := Derives.conjL (.conjR hi)
  exact .conjI (.conjL (.conjR hp)) (.conjL (.conjR (.conjR hp)))

theorem abstract_data_input {m} {Γ : Context m} (w a b A B f g u z n : Fin m)
    (hi : Derives Γ (abstractData w a b A B f g u z n)) : Derives Γ (abstractInput w a b A B) := by
  have hf := SyntaxVariableTableUnique.shifted_type true w a A b f (.conjL hi)
  have hs := SyntaxVariableTableUnique.shifted_successor true w a A b f (.conjL hi)
  have hp := Derives.conjR (.conjR (.conjR hi))
  exact .conjI (.conjI (.conjL hf) (.conjR (.conjL (.conjR hf))))
    (.conjI hs (.conjL (.conjR (.conjR hp))))

theorem instantiate_maps {m} {Γ : Context m} (w a b A t f g : Fin m)
    (hi : Derives Γ (instantiateEnv w a b A t f g)) : Derives Γ (SyntaxTermImageSyntax.maps w f g A b a b) := by
  let D := instantiateBody w a b A t f g
  let Δ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) hi
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := instantiate_data_maps w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m) hD
  exact of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) ho

theorem instantiate_input {m} {Γ : Context m} (w a b A t f g : Fin m)
    (hi : Derives Γ (instantiateEnv w a b A t f g)) : Derives Γ (instantiateInput w a b A t) := by
  let D := instantiateBody w a b A t f g
  let Δ := Context.add D (Context.image Formula.raise (Γ))
  apply Derives.exE (p := D) hi
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := instantiate_data_input w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc f.castSucc g.castSucc (Fin.last m) hD
  exact of_eq (by simp only [Formula.raise, instantiateInput_rename]) ho

theorem abstract_maps {m} {Γ : Context m} (w a b A B f g : Fin m)
    (hi : Derives Γ (abstractEnv w a b A B f g)) : Derives Γ (SyntaxTermImageSyntax.maps w f g a B A b) := by
  let D := abstractBody w a b A B f g
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ hi
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := abstract_data_maps w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hD
  exact of_eq (by simp only [Formula.raise, SyntaxTermImageSyntax.maps_rename]) ho

theorem abstract_input {m} {Γ : Context m} (w a b A B f g : Fin m)
    (hi : Derives Γ (abstractEnv w a b A B f g)) : Derives Γ (abstractInput w a b A B) := by
  let D := abstractBody w a b A B f g
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply eliminate_abstract w a b A B f g _ hi
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := abstract_data_input w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hD
  exact of_eq (by simp only [Formula.raise, abstractInput_rename]) ho

end PPAC.Migration.Internal.SyntaxTopEnvironmentTyping
