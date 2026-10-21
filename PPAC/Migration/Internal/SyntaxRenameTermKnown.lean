import PPAC.Migration.Internal.SyntaxRenameTerm

/-! 已知实际bvar/fvar原码时，重命名精确等价于对应真实图边及输入索引范围。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermKnown
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a n q i j : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code bound w i n)) (hq : Derives Γ (code bound w j q)) :
    Derives Γ ((branch bound w r a n q).iff ((Formula.mem i a).conj (edge r i j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := branch bound w r a n q
    let B := branchBody bound w r a n q
    let Ξ := Context.add R Γ
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Ξ))
    apply eliminate_branch bound w r a n q _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ R) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
      simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw R) B
    have hn2 : Derives Δ (code bound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := by
      simpa only [Formula.raise, code_rename] using OrderedPairElimination.under_two (add hn R) B
    have hq2 : Derives Δ (code bound w.castSucc.castSucc j.castSucc.castSucc q.castSucc.castSucc) := by
      simpa only [Formula.raise, code_rename] using OrderedPairElimination.under_two (add hq R) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hieq := SyntaxVariableDecode.index_eq hZ2 bound _ _ _ _ hw2 (.conjL (.conjR (.conjR hB))) hn2
    have hjeq := SyntaxVariableDecode.index_eq hZ2 bound _ _ _ _ hw2 (.conjR (.conjR (.conjR hB))) hq2
    have he1 := IterationValues.edge_subst_input r.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1))
      hieq (.conjL (.conjR hB))
    have he2 := GraphPointwiseSyntax.edge_subst_output _ _ _ _ hjeq he1
    have ho := Derives.conjI (mem_subst hieq (.conjL hB)) he2
    simpa only [Formula.raise, Formula.rename, edge_rename] using ho
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem i a).conj (edge r i j)) Γ) ((Formula.mem i a).conj (edge r i j)) := .hyp (Or.inl rfl)
    exact intro_branch bound w r a n q i j (.conjL hB) (.conjR hB) (add hn _) (add hq _)

theorem known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q i j : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (maps w r s a b c d)) (hn : Derives Γ (code bound w i n)) (hq : Derives Γ (code bound w j q)) :
    Derives Γ ((renamed w r s a b c d n q).iff
      ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (edge (selectMap bound r s) i j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := renamed w r s a b c d n q
    have hR : Derives (Context.add R Γ) R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ R
    have hw1 := add hw R
    have hn1 := add hn R
    have hq1 := add hq R
    cases bound
    · apply Derives.disjE (.conjR hR)
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ1 _) false w a n i
          (add hw1 _) (add hn1 _) (SyntaxRenameTermTyping.source_branch true w r a n q (.hyp (Or.inl rfl))))
      · exact .impE (.conjL (branch_iff (ZFContext.add hZ1 _) false w s b n q i j (add hw1 _) (add hn1 _) (add hq1 _))) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.conjR hR)
      · exact .impE (.conjL (branch_iff (ZFContext.add hZ1 _) true w r a n q i j (add hw1 _) (add hn1 _) (add hq1 _))) (.hyp (Or.inl rfl))
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ1 _) true w b n i
          (add hw1 _) (add hn1 _) (SyntaxRenameTermTyping.source_branch false w s b n q (.hyp (Or.inl rfl))))
  · apply Derives.impI
    let E := (Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (edge (selectMap bound r s) i j)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact intro_renamed bound w r s a b c d n q (add hm E)
      (intro_branch bound w (selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q i j
        (.conjL hE) (.conjR hE) (add hn E) (add hq E))

theorem reject_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q i j : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (maps w r s a b c d)) (hn : Derives Γ (code bound w i n)) (hq : Derives Γ (code bound w j q))
    (he : Derives Γ (edge (selectMap bound r s) i j).neg) : Derives Γ (renamed w r s a b c d n q).neg := by
  apply Derives.impI
  let R := renamed w r s a b c d n q
  have hh := known_iff (ZFContext.add hZ R) bound w r s a b c d n q i j (add hw R) (add hm R) (add hn R) (add hq R)
  exact .impE (add he _) (.conjR (.impE (.conjL hh) (.hyp (Or.inl rfl))))
end PPAC.Migration.Internal.SyntaxRenameTermKnown
