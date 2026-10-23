import PPAC.Migration.Internal.IndexFormulaRenameAtoms

/-! 子码归纳假设经过原binder的实际五个内部见证，传输无捕获公式调用。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameCheck
open Source SourceAlgebra SourceLogic OmegaSyntax IndexFormulaRenameBridgeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem intro_advanced {m} {Γ : Context m} (w x R S a b c d q A C K H : Fin m)
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hc : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.advanced w x R S a b c d q) := by
  apply Derives.exI A
  apply Derives.exI C
  apply Derives.exI K
  apply Derives.exI H
  exact of_eq (by simp only [SyntaxMixedFormulaRecursiveSyntax.advancedBody, Formula.instantiate, Formula.rename, SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hl hc)

theorem check_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w I J R S a b c d n x q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n))
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x I J a b c d q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x R S a b c d q) := by
  cases advance
  · exact transfer_child w I J R S a b c d n x q hi hx he hc
  · let B := SyntaxRenameRecursiveSyntax.advancedBody w x I J a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
    apply IndexFormulaRenameBinders.eliminate_three B _ hc
    have hZ3 := IndexFormulaRenameBinders.zf_under_three hZ B
    have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (IndexFormulaRenameBinders.under_three hw B)
    have he3 : Derives Δ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (IndexFormulaRenameBinders.under_three he B)
    have hi3 : Derives Δ (earlier w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (IndexFormulaRenameBinders.under_three hi B)
    have hx3 : Derives Δ (.mem x.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := IndexFormulaRenameBinders.under_three hx B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hSucc := SyntaxMapLiftParameters.successors w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (.conjL hB)
    have hLists := IndexTermImageCodeTyping.environment_lists w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc he3
    have hPair := SyntaxCodedMixedBinderExistence.exists_pair hZ3 w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (.conjI hLists hSucc)
    let E := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))
    let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Δ))
    apply SyntaxRenameBinders.eliminate_2 E _ hPair
    have hZ5 := SyntaxRenameBinders.zf_under_2 hZ3 E
    have hw5 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw3 E)
    have he5 : Derives Ξ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (SyntaxRenameBinders.under_2 he3 E)
    have hi5 : Derives Ξ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 hi3 E)
    have hx5 : Derives Ξ (.mem x.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc) := SyntaxRenameBinders.under_2 hx3 E
    have hB5 : Derives Ξ ((SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc).conj (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc)) :=
      of_eq (by simp only [B, SyntaxRenameRecursiveSyntax.advancedBody, Formula.raise, Formula.rename, SyntaxMapLiftSyntax.codedLift_rename, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 hB E)
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have hEnv := IndexTermCodedBinderTransport.coded_lift hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) hw5 he5 (.conjL hB5) hE
    have hChild := transfer_child w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) (Fin.last m).castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc hi5 hx5 hEnv (.conjR hB5)
    have ho : Derives Ξ (SyntaxMixedFormulaRecursiveSyntax.check true w.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc) :=
      intro_advanced w.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) hE hChild
    exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.check_rename]) ho

end PPAC.Migration.Internal.IndexFormulaRenameCheck
