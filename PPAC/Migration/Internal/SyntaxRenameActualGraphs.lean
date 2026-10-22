import PPAC.Migration.Internal.SyntaxRenameAtomUnique

/-! 任意候选解码图对齐给定实际完整图；将真实原子分支接回原 RenameFormula 判断。 -/
namespace PPAC.Migration.Internal.SyntaxRenameActualGraphs
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameBinders SyntaxMapCodeSyntax SyntaxRenameRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n q : Fin m)
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S)) :
    Derives Γ ((localRename w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let L := localRename w R S a b c d n q
    let B := localRenameBody w R S a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add L Γ)))
    apply eliminate_2 B _ (.hyp (Or.inl rfl))
    have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 (add hr L) B)
    have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 (add hs L) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have er := SyntaxMapCode.unique_graph (zf_under_2 (ZFContext.add hZ L) B) _ (Fin.last m).castSucc r.castSucc.castSucc _ _ _ (.conjL hB) hr2
    have es := SyntaxMapCode.unique_graph (zf_under_2 (ZFContext.add hZ L) B) _ (Fin.last (m+1)) s.castSucc.castSucc _ _ _ (.conjL (.conjR hB)) hs2
    have h0 := SyntaxRenameAtomicSubst.cases_r _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) _ _ _ _ _ _ r.castSucc.castSucc er (.conjR (.conjR hB))
    have h1 := SyntaxRenameAtomicSubst.cases_s _ _ _ r.castSucc.castSucc (Fin.last (m+1)) _ _ _ _ _ _ s.castSucc.castSucc es h0
    exact of_eq (by simp only [Formula.raise, cases_rename]) h1
  · apply Derives.impI
    exact intro_localRename w R S a b c d n q r s (.conjI (add hr _) (.conjI (add hs _) (.hyp (Or.inl rfl))))

theorem cases_of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) := by
  have hk := Derives.impE (.conjL (SyntaxRenameRecursive.recursive_iff hZ w R S a b c d n q hw)) hn
  exact .impE (.conjL (at_graphs hZ w R S r s a b c d n q hr hs)) (.conjR (.conjR (.conjR hk)))

theorem atomic_of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (arity : Nat)
    (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n))
    (hn : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) :
    Derives Γ (SyntaxRenameAtomicCases.atomicCase kind w r s a b c d n q) :=
  SyntaxRenameAtomicCases.filter hZ kind arity w R S r s a b c d n q xs hw hc
    (cases_of_renamed hZ w R S r s a b c d n q hw hr hs hn)

theorem intro_from_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w q c d))
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := by
  have hl := intro_localRename w R S a b c d n q r s (.conjI hr (.conjI hs hc))
  have hk : Derives Γ (criterion w R S a b c d n q) := .conjI
    (SyntaxRenameOutput.input_natural w R S a b c d n hi)
    (.conjI (.conjI (.conjL (.conjR hi)) (.conjI (.conjR (.conjR hi)) ht)) (.conjI (.conjL hi) hl))
  exact .impE (.conjR (SyntaxRenameRecursive.recursive_iff hZ w R S a b c d n q hw)) hk
end PPAC.Migration.Internal.SyntaxRenameActualGraphs
