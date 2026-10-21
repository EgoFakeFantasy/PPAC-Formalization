import PPAC.Migration.Internal.SyntaxRenameTermSyntax

/-! 真实重命名的输入/输出作用域保持；完整图的值域检查给目标索引范围。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermTyping
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
open SyntaxTermSyntax (term contexts term_rename branch_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem source_branch {m} {Γ : Context m} (bound : Bool) (w r a n q : Fin m)
    (hh : Derives Γ (branch bound w r a n q)) : Derives Γ (SyntaxTermSyntax.branch bound w a n) := by
  let B := branchBody bound w r a n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_branch bound w r a n q _ hh
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxTermSyntax.intro_branch bound w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc
    (Fin.last m).castSucc (.conjL hB) (.conjL (.conjR (.conjR hB)))
  simpa only [Formula.raise, SyntaxTermSyntax.branch_rename] using ho

theorem target_branch {m} {Γ : Context m} (bound : Bool) (w r a c n q : Fin m)
    (hm : Derives Γ (indexMap w r a c)) (hh : Derives Γ (branch bound w r a n q)) :
    Derives Γ (SyntaxTermSyntax.branch bound w c q) := by
  let B := branchBody bound w r a n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_branch bound w r a n q _ hh
  have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, indexMap_rename] using OrderedPairElimination.under_two hm B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hj := edge_target _ _ _ _ _ _ hm2 (.conjL (.conjR hB))
  have ho := SyntaxTermSyntax.intro_branch bound w.castSucc.castSucc c.castSucc.castSucc q.castSucc.castSucc
    (Fin.last (m+1)) hj (.conjR (.conjR (.conjR hB)))
  simpa only [Formula.raise, SyntaxTermSyntax.branch_rename] using ho

theorem source_term {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hh : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (term w a b n) := by
  have hc := source_contexts w r s a b c d (.conjL hh)
  apply Derives.conjI hc
  apply Derives.disjE (.conjR hh)
  · exact .disjL (source_branch true w r a n q (.hyp (Or.inl rfl)))
  · exact .disjR (source_branch false w s b n q (.hyp (Or.inl rfl)))

theorem target_term {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hh : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (term w c d q) := by
  have hc := target_contexts w r s a b c d (.conjL hh)
  apply Derives.conjI hc
  apply Derives.disjE (.conjR hh)
  · exact .disjL (target_branch true w r a c n q (add (.conjL (.conjL hh)) _) (.hyp (Or.inl rfl)))
  · exact .disjR (target_branch false w s b d n q (add (.conjR (.conjL hh)) _) (.hyp (Or.inl rfl)))

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (.mem q w) :=
  SyntaxTerms.range hZ w c d q hw (target_term w r s a b c d n q hh)

theorem opposite_branches {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b n q v : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (branch true w r a n q))
    (hf : Derives Γ (branch false w s b n v)) : Derives Γ .bot :=
  SyntaxTermBranches.exclusive hZ w a b n hw (source_branch true w r a n q hb) (source_branch false w s b n v hf)
end PPAC.Migration.Internal.SyntaxRenameTermTyping
