import PPAC.Migration.Internal.IndexTermAtomTransport

/-! 已知源变量及实际索引边时，重命名的任意候选输出精确等价于目标变量码。 -/
namespace PPAC.Migration.Internal.IndexVariableTermReading
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_source_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w r a c n q i j : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c))
    (hn : Derives Γ (code isBound w i n)) (he : Derives Γ (edge r i j)) :
    Derives Γ ((branch isBound w r a n q).iff (code isBound w j q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := branch isBound w r a n q
    let B := branchBody isBound w r a n q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add R Γ)))
    apply eliminate_branch isBound w r a n q _ (.hyp (Or.inl rfl))
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ R) B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw R) B)
    have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (SyntaxRenameBinders.under_2 (add hm R) B)
    have hn2 : Derives Δ (code isBound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, code_rename]) (SyntaxRenameBinders.under_2 (add hn R) B)
    have he2 : Derives Δ (edge r.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc) := of_eq (by simp only [Formula.raise, edge_rename]) (SyntaxRenameBinders.under_2 (add he R) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hIndex := SyntaxVariableDecode.index_eq hZ2 isBound w.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL (.conjR (.conjR hB))) hn2
    have hEdge := IterationValues.edge_subst_input r.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1)) hIndex (.conjL (.conjR hB))
    have hTarget := GraphProperties.single_valued r.castSucc.castSucc a.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) j.castSucc.castSucc (ZFContext.arithmetic hZ2).base.extensionality (.conjL (.conjR hm2)) hEdge he2
    have ho := code_index_subst isBound w.castSucc.castSucc (Fin.last (m+1)) j.castSucc.castSucc q.castSucc.castSucc hTarget (.conjR (.conjR (.conjR hB)))
    exact of_eq (by simp only [Formula.raise, code_rename]) ho
  · apply Derives.impI
    let C := code isBound w j q
    exact intro_branch isBound w r a n q i j (edge_source (ZFContext.add hZ C) w r a c i j (add hm C) (add he C)) (add he C) (add hn C) (.hyp (Or.inl rfl))

theorem source_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w r s a b c d n q i j : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hn : Derives Γ (code isBound w i n)) (he : Derives Γ (edge (selectMap isBound r s) i j)) :
    Derives Γ ((renamed w r s a b c d n q).iff (code isBound w j q)) := by
  have hMap := selected isBound w r s a b c d hm
  apply Derives.conjI
  · apply Derives.impI
    let R := renamed w r s a b c d n q
    have hR : Derives (Context.add R Γ) R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ R
    cases isBound
    · apply Derives.disjE (.conjR hR)
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ1 _) false w a n i (add (add hw R) _) (add (add hn R) _) (SyntaxRenameTermTyping.source_branch true w r a n q (.hyp (Or.inl rfl))))
      · exact .impE (.conjL (branch_source_iff (ZFContext.add hZ1 _) false w s b d n q i j (add (add hw R) _) (add (add hMap R) _) (add (add hn R) _) (add (add he R) _))) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.conjR hR)
      · exact .impE (.conjL (branch_source_iff (ZFContext.add hZ1 _) true w r a c n q i j (add (add hw R) _) (add (add hMap R) _) (add (add hn R) _) (add (add he R) _))) (.hyp (Or.inl rfl))
      · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ1 _) true w b n i (add (add hw R) _) (add (add hn R) _) (SyntaxRenameTermTyping.source_branch false w s b n q (.hyp (Or.inl rfl))))
  · apply Derives.impI
    let C := code isBound w j q
    have hb := Derives.impE (.conjR (branch_source_iff (ZFContext.add hZ C) isBound w (selectMap isBound r s) (SyntaxTermSyntax.limit isBound a b) (SyntaxTermSyntax.limit isBound c d) n q i j (add hw C) (add hMap C) (add hn C) (add he C))) (.hyp (Or.inl rfl))
    exact intro_renamed isBound w r s a b c d n q (add hm C) hb

theorem variable_output_subst {m} {Γ : Context m} (isBound : Bool) (w i n q : Fin m)
    (he : Derives Γ (.equal n q)) (hn : Derives Γ (code isBound w i n)) : Derives Γ (code isBound w i q) := by
  let F := code isBound w.castSucc i.castSucc (Fin.last m)
  have h0 : F.instantiate n = code isBound w i n := by simp only [F, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : F.instantiate q = code isBound w i q := by simp only [F, Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst F he (of_eq h0.symm hn))

theorem equality_iff_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w i n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code isBound w i n)) : Derives Γ ((Formula.equal q n).iff (code isBound w i q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact variable_output_subst isBound w i n q (eq_symm (.hyp (Or.inl rfl))) (add hn _)
  · apply Derives.impI
    exact eq_symm (SyntaxVariables.unique (ZFContext.add hZ _) isBound w i n q (add hw _) (add hn _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.IndexVariableTermReading
