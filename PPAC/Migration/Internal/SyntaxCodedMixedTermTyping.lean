import PPAC.Migration.Internal.SyntaxCodedMixedTermGraphs

/-! 原数值环境参数的混合项替换具有准确源/目标项类型和纯合法输入。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax

theorem source_type {m} {Γ : Context m} (w R S a b c d n q : Fin m) (hq : Derives Γ (substituted w R S a b c d n q)) :
    Derives Γ (SyntaxTermSyntax.term w a b n) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedTermTyping.source_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hB)
  exact of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) ho

theorem target_type {m} {Γ : Context m} (w R S a b c d n q : Fin m) (hq : Derives Γ (substituted w R S a b c d n q)) :
    Derives Γ (SyntaxTermSyntax.term w c d q) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedTermTyping.target_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hB)
  exact of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) ho

theorem output_natural {m} {Γ : Context m} (w R S a b c d n q : Fin m) (hq : Derives Γ (substituted w R S a b c d n q)) :
    Derives Γ (Formula.mem q w) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedTermTyping.output_natural w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.rename]) ho

theorem input_of_substituted {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hq : Derives Γ (substituted w R S a b c d n q)) : Derives Γ (input w R S a b c d n) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := SyntaxMixedTermTyping.source_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hB)
  have hl := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (.conjL hB)
  have ho : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) := .conjI hl hs
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

end PPAC.Migration.Internal.SyntaxCodedMixedTermTyping
