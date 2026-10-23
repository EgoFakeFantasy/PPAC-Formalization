import PPAC.Migration.Internal.IndexFormulaRenameCases

/-! 全部内部元数据的传输推进，不保留外部公式结构或编码前提。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenamePoint
open Source SourceAlgebra SourceLogic OmegaSyntax IndexFormulaRenameBridgeSyntax SyntaxRenameBinders
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem local_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n)) (hl : Derives Γ (SyntaxRenameRecursiveSyntax.localRename w I J a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q) := by
  let B := SyntaxRenameRecursiveSyntax.localRenameBody w I J a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_2 B _ hl
  have hZ2 := zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have he2 : Derives Δ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (under_2 he B)
  have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := IndexFormulaRenameCases.cases_forward hZ2 w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc hw2 he2 hi2 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.cases_rename]) ho

theorem forward_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n)) (ho : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hc := Derives.impE (.conjL (SyntaxRenameRecursive.recursive_iff hZ w I J a b c d n q hw)) ho
  have hCases := local_cases hZ w I J R S a b c d n q hw he hi (.conjR (.conjR (.conjR hc)))
  have hTarget := SyntaxRenameJudgment.target_type w I J a b c d n q ho
  have hLists := IndexTermImageCodeTyping.environment_lists w I J R S a b c d he
  exact .impE (.conjR (SyntaxMixedFormulaRecursive.recursive_iff hZ w R S a b c d n q hw))
    (.conjI (.conjL hc) (.conjI (.conjI hLists hTarget) (.conjI (.conjL (.conjR (.conjR hc))) hCases)))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let E := IndexTermImageCodeSyntax.environment w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc (Fin.last (m+7)).castSucc
  let O := SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc (Fin.last (m+7)).castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8))
  let Δ := Context.add O (Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))))))))
  have hZ9 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) E) O
  have hw9 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))))))))) E) O)
  have hi9 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [earlier_rename]) (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hi))))))))) E) O)
  exact forward_from_earlier hZ9 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc (Fin.last (m+7)).castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)) hw9 (.hyp (Or.inr (Or.inl rfl))) hi9 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.IndexFormulaRenamePoint
