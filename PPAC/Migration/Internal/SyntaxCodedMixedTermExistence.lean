import PPAC.Migration.Internal.SyntaxCodedMixedTermTyping

/-! 每个合法原数值混合环境及源项实际取得替换结果，解码图与结果均为对象见证。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n)) : Derives Γ (existsOutput w R S a b c d n) := by
  let G := SyntaxMixedImageCodePairs.graphBody w a b c d R S
  let Ξ := Context.add G (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex G)) := SyntaxMixedImageCodePairs.exists_graphs hZ w a b c d R S hw (.conjL hi)
  apply SyntaxRenameBinders.eliminate_2 G _ he
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hn2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 (.conjR hi) G)
  have hm := SyntaxMixedImageCodePairs.image_maps w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc hG
  let Q := SyntaxMixedTermSyntax.substituted w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) (SyntaxMixedTermExistence.exists_output w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (.conjI hm hn2))
  have hg3 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [G, SyntaxMixedImageCodePairs.graphBody, Formula.raise, SyntaxMixedImageCodeSyntax.encodings_rename]) (under hG Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hs := intro_substituted w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hg3 hQ
  have ho := intro_exists w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) hs
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

end PPAC.Migration.Internal.SyntaxCodedMixedTermExistence
