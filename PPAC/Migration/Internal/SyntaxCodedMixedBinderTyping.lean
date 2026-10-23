import PPAC.Migration.Internal.SyntaxCodedMixedBinderUnique

/-! 原数值混合binder的纯输入/输出列表类型与准确后继输入；不残留解码图假设。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax

theorem input_lists {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (.conjL hB)
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) ho

theorem output_lists {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w A b C d K H) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) ho

theorem input_of_lifted {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (input w R S a b c d A C) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxMixedImageBinderFiber.input_of_lifted w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjL (.conjR hB))
  have hL := SyntaxMixedImageCodePairs.term_lists w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (.conjL hB)
  have ho : Derives Δ (input w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc) := .conjI hL (.conjR hi)
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

theorem output_natural {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ ((Formula.mem K w).conj (Formula.mem H w)) := by
  have hs := output_lists w R S a b c d A C K H hl
  exact .conjI (.conjL (.conjL (.conjR (.conjR (.conjL hs)))) ) (.conjL (.conjL (.conjR (.conjR (.conjR hs)))))

end PPAC.Migration.Internal.SyntaxCodedMixedBinderTyping
