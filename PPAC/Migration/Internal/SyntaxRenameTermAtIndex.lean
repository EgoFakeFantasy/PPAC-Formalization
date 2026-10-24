import PPAC.Migration.Internal.SyntaxRenameTermKnown
import PPAC.Migration.Internal.SyntaxRenameQuerySyntax

/-! 已知实际索引图边时，对全部内部候选输出的变量重命名双条件。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermAtIndex
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem branch_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r a n q i j : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (functionOn r a)) (hi : Derives Γ (.mem i a))
    (he : Derives Γ (edge r i j)) (hn : Derives Γ (code bound w i n)) :
    Derives Γ ((branch bound w r a n q).iff (code bound w j q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := branch bound w r a n q
    let B := branchBody bound w r a n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    apply eliminate_branch bound w r a n q _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ E) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two (add hw E) B)
    have hr2 : Derives Δ (functionOn r.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, functionOn_rename]) (OrderedPairElimination.under_two (add hr E) B)
    have he2 : Derives Δ (edge r.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc) := of_eq (by simp only [Formula.raise, edge_rename]) (OrderedPairElimination.under_two (add he E) B)
    have hn2 : Derives Δ (code bound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, code_rename]) (OrderedPairElimination.under_two (add hn E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hp := SyntaxVariableDecode.index_eq hZ2 bound _ _ _ _ hw2 (.conjL (.conjR (.conjR hB))) hn2
    have hed := IterationValues.edge_subst_input r.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1)) hp (.conjL (.conjR hB))
    have hj := GraphProperties.single_valued r.castSucc.castSucc a.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) j.castSucc.castSucc
      (ZFContext.arithmetic hZ2).base.extensionality hr2 hed he2
    have ho := code_index_subst bound w.castSucc.castSucc (Fin.last (m+1)) j.castSucc.castSucc q.castSucc.castSucc hj (.conjR (.conjR (.conjR hB)))
    exact of_eq (by simp only [Formula.raise, code_rename]) ho
  · exact .impI (intro_branch bound w r a n q i j (add hi _) (add he _) (add hn _) (.hyp (Or.inl rfl)))

theorem renamed_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q i j : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (maps w r s a b c d)) (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (he : Derives Γ (edge (selectMap bound r s) i j)) (hn : Derives Γ (code bound w i n)) :
    Derives Γ ((renamed w r s a b c d n q).iff (code bound w j q)) := by
  have hr : Derives Γ (functionOn (selectMap bound r s) (SyntaxTermSyntax.limit bound a b)) := by
    cases bound
    · exact .conjL (.conjR (.conjR hm))
    · exact .conjL (.conjR (.conjL hm))
  have hb := branch_at hZ bound w (selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q i j hw hr hi he hn
  apply Derives.conjI
  · apply Derives.impI
    let E := renamed w r s a b c d n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    cases bound
    · apply Derives.disjE (.conjR hE)
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add (ZFContext.add hZ E) _) false w a n i
          (add (add hw E) _) (add (add hn E) _) (SyntaxRenameTermTyping.source_branch true w r a n q (.hyp (Or.inl rfl))))
      · exact .impE (add (add (.conjL hb) E) _) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.conjR hE)
      · exact .impE (add (add (.conjL hb) E) _) (.hyp (Or.inl rfl))
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add (ZFContext.add hZ E) _) true w b n i
          (add (add hw E) _) (add (add hn E) _) (SyntaxRenameTermTyping.source_branch false w s b n q (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact intro_renamed bound w r s a b c d n q (add hm _) (.impE (add (.conjR hb) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.SyntaxRenameTermAtIndex
