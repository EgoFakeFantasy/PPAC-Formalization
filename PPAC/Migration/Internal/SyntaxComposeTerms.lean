import PPAC.Migration.Internal.SyntaxComposeCodeUnique

/-! 两次实际图重命名的项复合；bound/free模式保持，允许非单射输入。 -/
namespace PPAC.Migration.Internal.SyntaxComposeTerms
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxIndexMapSyntax SyntaxComposeSyntax
open SyntaxVariableSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_compose {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r t a c e g n q v : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hfirst : Derives Γ (branch bound w r a n q)) (hsecond : Derives Γ (branch bound w t c q v)) :
    Derives Γ (branch bound w g a n v) := by
  let B := branchBody bound w r a n q
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_branch bound w r a n q _ hfirst
  have hs2 : Derives Ξ (branch bound w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, branch_rename]) (SyntaxRenameBinders.under_2 hsecond B)
  let C := branchBody bound w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_branch bound w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc _ hs2
  have hZ4 := SyntaxRenameBinders.zf_under_2 (SyntaxRenameBinders.zf_under_2 hZ B) C
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hw B) C)
  have hg4 : Derives Δ (composed w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (SyntaxRenameBinders.under_2 (SyntaxRenameBinders.under_2 hg B) C)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb4 : Derives Δ ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc).conj ((edge r.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj ((code bound w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc).conj (code bound w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc)))) := of_eq (by simp only [B, branchBody, Formula.raise, Formula.rename, edge_rename, code_rename]) (SyntaxRenameBinders.under_2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have heq := SyntaxVariableDecode.index_eq hZ4 bound w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hw4 (.conjL (.conjR (.conjR hC))) (.conjR (.conjR (.conjR hb4)))
  have ht := IterationValues.edge_subst_input _ _ _ _ heq (.conjL (.conjR hC))
  have hv := intro_value _ _ _ _ _ (.conjL (.conjR hb4)) ht
  have edgeG := Derives.impE (.conjR (SyntaxComposeGraph.edge_iff hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+3)) hg4)) hv
  have ho := intro_branch bound w.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+3)) (.conjL hb4) edgeG (.conjL (.conjR (.conjR hb4))) (.conjR (.conjR (.conjR hC)))
  exact of_eq (by simp only [Formula.raise, branch_rename]) ho

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g)) (hh : Derives Γ (composed w s u b d f h))
    (hfirst : Derives Γ (renamed w r s a b c d n q)) (hsecond : Derives Γ (renamed w t u c d e f q v)) :
    Derives Γ (renamed w g h a b e f n v) := by
  have hm := Derives.conjI (SyntaxComposeGraph.target_map _ _ _ _ _ _ _ hg) (SyntaxComposeGraph.target_map _ _ _ _ _ _ _ hh)
  apply Derives.disjE (.conjR hfirst)
  · let X := branch true w r a n q
    have hX : Derives (Context.add X Γ) X := .hyp (Or.inl rfl)
    apply Derives.disjE (.conjR (add hsecond X))
    · exact intro_renamed true w g h a b e f n v (add (add hm X) _)
        (branch_compose (ZFContext.add (ZFContext.add hZ X) _) true w r t a c e g n q v (add (add hw X) _) (add (add hg X) _) (add hX _) (.hyp (Or.inl rfl)))
    · let Y := branch false w u d q v
      exact .botE (SyntaxTermBranches.exclusive (ZFContext.add (ZFContext.add hZ X) Y) w c d q (add (add hw X) Y)
        (SyntaxRenameTermTyping.target_branch true w r a c n q (add (add (.conjL hg) X) Y) (add hX Y))
        (SyntaxRenameTermTyping.source_branch false w u d q v (.hyp (Or.inl rfl))))
  · let X := branch false w s b n q
    have hX : Derives (Context.add X Γ) X := .hyp (Or.inl rfl)
    apply Derives.disjE (.conjR (add hsecond X))
    · let Y := branch true w t c q v
      exact .botE (SyntaxTermBranches.exclusive (ZFContext.add (ZFContext.add hZ X) Y) w c d q (add (add hw X) Y)
        (SyntaxRenameTermTyping.source_branch true w t c q v (.hyp (Or.inl rfl)))
        (SyntaxRenameTermTyping.target_branch false w s b d n q (add (add (.conjL hh) X) Y) (add hX Y)))
    · exact intro_renamed false w g h a b e f n v (add (add hm X) _)
        (branch_compose (ZFContext.add (ZFContext.add hZ X) _) false w s u b d f h n q v (add (add hw X) _) (add (add hh X) _) (add hX _) (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.SyntaxComposeTerms
