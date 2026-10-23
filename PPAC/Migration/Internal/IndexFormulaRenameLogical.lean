import PPAC.Migration.Internal.IndexFormulaRenameCheck

/-! 全部逻辑构造的实际子判断传输；子码严格界来自原检查器。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameLogical
open Source SourceAlgebra SourceLogic OmegaSyntax IndexFormulaRenameBridgeSyntax SyntaxRenameBinders
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n))
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.single tag advance w I J a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w R S a b c d n q) := by
  let B := SyntaxRenameRecursiveSyntax.singleBody tag advance w I J a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_2 B _ hc
  have hZ2 := zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have he2 : Derives Δ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (under_2 he B)
  have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hCheck := IndexFormulaRenameCheck.check_forward hZ2 advance w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 he2 hi2 (.conjL (.conjR hB)) (.conjR (.conjR (.conjR hB)))
  have ho := SyntaxMixedFormulaRecursiveSyntax.intro_single tag advance w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjI (.conjL hB) (.conjI (.conjL (.conjR hB)) (.conjI (.conjL (.conjR (.conjR hB))) hCheck)))
  exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.single_rename]) ho

theorem binary_forward {m} {Γ : Context m} (kind : Fin 4) (w I J R S a b c d n q : Fin m)
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n))
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.binary kind w I J a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w R S a b c d n q) := by
  let B := SyntaxRenameRecursiveSyntax.binaryBody kind w I J a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_4 B _ hc
  have he4 : Derives Δ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (under_4 he B)
  have hi4 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_4 hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hX := transfer_child w.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hi4 (.conjL (.conjR hB)) he4 (.conjL (.conjR (.conjR (.conjR (.conjR hB)))))
  have hY := transfer_child w.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) hi4 (.conjL (.conjR (.conjR hB))) he4 (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have ho := SyntaxMixedFormulaRecursiveSyntax.intro_binary kind w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjI (.conjL hB) (.conjI (.conjL (.conjR hB)) (.conjI (.conjL (.conjR (.conjR hB))) (.conjI (.conjL (.conjR (.conjR (.conjR hB)))) (.conjI hX hY)))))
  exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.binary_rename]) ho

end PPAC.Migration.Internal.IndexFormulaRenameLogical
