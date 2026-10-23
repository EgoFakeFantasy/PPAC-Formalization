import PPAC.Migration.Internal.SyntaxCodedMixedBinderGraphs

/-! 实际构造原数值混合环境的binder输出码对，四张表及两个输出码皆在对象量词内。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d A C)) : Derives Γ (existsPair w R S a b c d A C) := by
  let G := SyntaxMixedImageCodePairs.graphBody w a b c d R S
  let Ξ := Context.add G (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex G)) := SyntaxMixedImageCodePairs.exists_graphs hZ w a b c d R S hw (.conjL hi)
  apply SyntaxRenameBinders.eliminate_2 G _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ G
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw G)
  have hi2 : Derives Ξ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc) := of_eq (by simp only [Formula.raise, input_rename]) (SyntaxRenameBinders.under_2 hi G)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hm := SyntaxMixedImageCodePairs.image_maps w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc hG
  let B := SyntaxMixedImageBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
  let Ψ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Ξ))
  have hb : Derives Ξ (.ex (.ex B)) := SyntaxMixedImageBinderOutput.exists_pair hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc hw2 hm (.conjL (.conjR hi2)) (.conjR (.conjR hi2))
  apply SyntaxRenameBinders.eliminate_2 B _ hb
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 B
  have hw4 : Derives Ψ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 B)
  have hB : Derives Ψ B := .hyp (Or.inl rfl)
  have hoMaps := SyntaxMixedImageBinderOutput.target_maps w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hB
  let O := SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5))
  let Δ := Context.add O (Context.image Formula.raise (Context.image Formula.raise Ψ))
  have hoc : Derives Ψ (.ex (.ex O)) := SyntaxMixedImageCodePairs.exists_codes hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc hw4 hoMaps
  apply SyntaxRenameBinders.eliminate_2 O _ hoc
  have hg6 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [G, SyntaxMixedImageCodePairs.graphBody, Formula.raise, SyntaxMixedImageCodeSyntax.encodings_rename])
      (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hG B) O)
  have hb6 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc) :=
    of_eq (by simp only [B, Formula.raise, SyntaxMixedImageBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hB O)
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have hp : Derives Δ (state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc) := .conjI hg6 (.conjI hb6 hO)
  have hl := intro_lifted w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc hp
  have ho := intro_pair w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) hl
  exact of_eq (by simp only [Formula.raise, existsPair_rename]) ho

end PPAC.Migration.Internal.SyntaxCodedMixedBinderExistence
