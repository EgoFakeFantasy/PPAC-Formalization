import PPAC.Migration.Internal.SyntaxRenameTermTyping

/-! 非单射索引映射下输出仍唯一；源索引由原码单射性恢复，不假设映射单射。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_indices {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r a n q v i j k t : Fin m) (hw : Derives Γ (omega w)) (hr : Derives Γ (functionOn r a))
    (hi : Derives Γ (code bound w i n)) (hk : Derives Γ (code bound w k n))
    (hij : Derives Γ (edge r i j)) (hkt : Derives Γ (edge r k t))
    (hq : Derives Γ (code bound w j q)) (hv : Derives Γ (code bound w t v)) : Derives Γ (.equal q v) := by
  have hik := SyntaxVariableDecode.index_eq hZ bound w i k n hw hi hk
  have hnew := IterationValues.edge_subst_input r k i t (eq_symm hik) hkt
  have hjt := GraphProperties.single_valued r a i j t (ZFContext.arithmetic hZ).base.extensionality hr hij hnew
  have hq2 := code_index_subst bound w j t q hjt hq
  exact SyntaxVariables.unique hZ bound w t q v hw hq2 hv

theorem branch_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a n q v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (functionOn r a))
    (hq : Derives Γ (branch bound w r a n q)) (hv : Derives Γ (branch bound w r a n v)) :
    Derives Γ (.equal q v) := by
  let Q := branchBody bound w r a n q
  let Ξ := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_branch bound w r a n q _ hq
  have hv2 : Derives Ξ (branch bound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, branch_rename] using OrderedPairElimination.under_two hv Q
  let V := branchBody bound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_branch bound w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc _ hv2
  have hZ4 := ZFContext.under_two (ZFContext.under_two hZ Q) V
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (OrderedPairElimination.under_two hw Q) V
  have hr4 : Derives Δ (functionOn r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using OrderedPairElimination.under_two (OrderedPairElimination.under_two hr Q) V
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hQ4 : Derives Δ
      ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc).conj
        ((edge r.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).conj
          ((code bound w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc).conj
            (code bound w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc)))) := by
    simpa only [Q, branchBody, Formula.raise, Formula.rename, edge_rename, code_rename] using OrderedPairElimination.under_two hQ V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  exact at_indices hZ4 bound _ _ _ _ _ _ _ _ _ _ hw4 hr4
    (.conjL (.conjR (.conjR hQ4))) (.conjL (.conjR (.conjR hV)))
    (.conjL (.conjR hQ4)) (.conjL (.conjR hV))
    (.conjR (.conjR (.conjR hQ4))) (.conjR (.conjR (.conjR hV)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (renamed w r s a b c d n q))
    (hv : Derives Γ (renamed w r s a b c d n v)) : Derives Γ (.equal q v) := by
  apply Derives.disjE (.conjR hq)
  · let B := branch true w r a n q
    have hB : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
    apply Derives.disjE (add (.conjR hv) B)
    · exact branch_unique (ZFContext.add (ZFContext.add hZ B) _) true w r a n q v
        (add (add hw B) _) (add (add (.conjL (.conjR (.conjL (.conjL hq)))) B) _) (add hB _) (.hyp (Or.inl rfl))
    · exact .botE (SyntaxRenameTermTyping.opposite_branches (ZFContext.add (ZFContext.add hZ B) _)
        w r s a b n q v (add (add hw B) _) (add hB _) (.hyp (Or.inl rfl)))
  · let F := branch false w s b n q
    have hF : Derives (Context.add F Γ) F := .hyp (Or.inl rfl)
    apply Derives.disjE (add (.conjR hv) F)
    · exact .botE (SyntaxRenameTermTyping.opposite_branches (ZFContext.add (ZFContext.add hZ F) _)
        w r s a b n v q (add (add hw F) _) (.hyp (Or.inl rfl)) (add hF _))
    · exact branch_unique (ZFContext.add (ZFContext.add hZ F) _) false w s b n q v
        (add (add hw F) _) (add (add (.conjL (.conjR (.conjR (.conjL hq)))) F) _) (add hF _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxRenameTermUnique
