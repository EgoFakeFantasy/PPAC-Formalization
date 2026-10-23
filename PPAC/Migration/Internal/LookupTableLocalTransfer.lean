import PPAC.Migration.Internal.LookupTableProgramFacts

/-! 原Cons严格tail界把实际历史查询传到新程序自己的子执行，无外部标准性前提。 -/
namespace PPAC.Migration.Internal.LookupTableLocalTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hg : Derives Γ (LookupTableRecursionSyntax.graph w h n))
    (hs : Derives Γ (LookupTableProgramSyntax.successorCase w h n i y)) : Derives Γ (LookupTableRecursiveSyntax.successorCase w n i y) := by
  let B := LookupTableProgramSyntax.successorBody w h n i y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hs
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hg2 : Derives Δ (LookupTableRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, LookupTableRecursionSyntax.graph_rename]) (SyntaxRenameBinders.under_2 hg B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOrd := NaturalOrderBasic.ordinal hZ2 w.castSucc.castSucc n.castSucc.castSucc hw2 (SyntaxRenameBinders.under_2 hn B)
  have ht := LookupTableProgramFacts.tail_member hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjL hB)
  have htW := StructuralListProjection.selected_range false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (.conjL hB)
  have hRead := LookupTableJudgment.read_iff hZ2 w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc hOrd ht htW hg2
  have ho := LookupTableRecursiveSyntax.intro_successor w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hB) (.conjL (.conjL (.conjR hB))) (.conjR (.conjL (.conjR hB))) (.impE (.conjL hRead) (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, LookupTableRecursiveSyntax.successorCase_rename]) ho

theorem successor_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hg : Derives Γ (LookupTableRecursionSyntax.graph w h n))
    (hs : Derives Γ (LookupTableRecursiveSyntax.successorCase w n i y)) : Derives Γ (LookupTableProgramSyntax.successorCase w h n i y) := by
  let B := LookupTableRecursiveSyntax.successorBody w n i y
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hs
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hg2 : Derives Δ (LookupTableRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, LookupTableRecursionSyntax.graph_rename]) (SyntaxRenameBinders.under_2 hg B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOrd := NaturalOrderBasic.ordinal hZ2 w.castSucc.castSucc n.castSucc.castSucc hw2 (SyntaxRenameBinders.under_2 hn B)
  have ht := LookupTableProgramFacts.tail_member hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjL hB)
  have htW := StructuralListProjection.selected_range false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (.conjL hB)
  have hRead := LookupTableJudgment.read_iff hZ2 w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc hOrd ht htW hg2
  have ho := LookupTableProgramSyntax.intro_successor w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hB) (.conjL (.conjL (.conjR hB))) (.conjR (.conjL (.conjR hB))) (.impE (.conjR hRead) (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, LookupTableProgramSyntax.successorCase_rename]) ho

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (LookupTableRecursionSyntax.graph w h n)) :
    Derives Γ ((LookupTableProgramSyntax.successorCase w h n i y).iff (LookupTableRecursiveSyntax.successorCase w n i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) w h n i y (add hw _) (add hn _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ZFContext.add hZ _) w h n i y (add hw _) (add hn _) (add hg _) (.hyp (Or.inl rfl))

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h n i y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (LookupTableRecursionSyntax.graph w h n)) :
    Derives Γ ((LookupTableProgramSyntax.run w h n i y).iff (LookupTableRecursiveSyntax.step w n i y)) :=
  SyntaxTypeLocalTransfer.disj_congr (SyntaxTypeLocalTransfer.iff_refl (LookupTableProgramSyntax.zeroCase w n i y))
    (successor_iff hZ w h n i y hw hn hg)

end PPAC.Migration.Internal.LookupTableLocalTransfer
