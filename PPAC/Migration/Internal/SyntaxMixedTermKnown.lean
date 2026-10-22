import PPAC.Migration.Internal.SyntaxMixedTermTyping

/-! 已知原源变量码时混合替换精确等价实际项像表边；目标类别保持任意。 -/
namespace PPAC.Migration.Internal.SyntaxMixedTermKnown
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedTermSyntax
open SyntaxVariableSyntax (code code_rename)
open SyntaxTermImageSyntax (maps maps_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w f a n q i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) :
    Derives Γ ((branch bound w f a n q).iff ((Formula.mem i a).conj (edge f i q))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := branch bound w f a n q
    let B := branchBody bound w f a n q
    let Δ := Context.add B (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw H) B)
    have hc1 : Derives Δ (code bound w.castSucc i.castSucc n.castSucc) := of_eq (code_rename bound w i n Fin.castSucc) (under (add hc H) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := SyntaxVariableDecode.index_eq (ZFContext.under (ZFContext.add hZ H) B) bound _ _ _ _ hw1 (.conjL (.conjR hB)) hc1
    have ho : Derives Δ ((Formula.mem i.castSucc a.castSucc).conj (edge f.castSucc i.castSucc q.castSucc)) :=
      .conjI (mem_subst he (.conjL hB)) (IterationValues.edge_subst_input _ _ _ _ he (.conjR (.conjR hB)))
    exact of_eq (by simp only [Formula.raise, Formula.rename, edge_rename]) ho
  · apply Derives.impI
    have h : Derives (Context.add ((Formula.mem i a).conj (edge f i q)) Γ) ((Formula.mem i a).conj (edge f i q)) := .hyp (Or.inl rfl)
    exact intro_branch bound w f a n q i (.conjL h) (add hc _) (.conjR h)

theorem opposite {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w f a n q i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n))
    (hb : Derives Γ (branch (!bound) w f a n q)) : Derives Γ .bot := by
  let B := branchBody (!bound) w f a n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (code bound w.castSucc i.castSucc n.castSucc) := of_eq (code_rename bound w i n Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxVariableDecode.opposite_disjoint (ZFContext.under hZ B) bound _ _ _ _ hw1 hc1 (.conjL (.conjR hB))

theorem branch_of_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q i : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n))
    (hq : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (branch bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q) := by
  cases bound with
  | false =>
    apply Derives.disjE (.conjR hq)
    · exact .botE (opposite (ZFContext.add hZ _) false w r a n q i (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    · exact .hyp (Or.inl rfl)
  | true =>
    apply Derives.disjE (.conjR hq)
    · exact .hyp (Or.inl rfl)
    · exact .botE (opposite (ZFContext.add hZ _) true w s b n q i (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r s a b c d n q i : Fin m) (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hc : Derives Γ (code bound w i n)) : Derives Γ ((substituted w r s a b c d n q).iff
      ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (edge (SyntaxIndexMapSyntax.selectMap bound r s) i q))) := by
  have hk := branch_iff hZ bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q i hw hc
  apply Derives.conjI
  · apply Derives.impI
    have hb := branch_of_code (ZFContext.add hZ _) bound w r s a b c d n q i (add hw _) (add hc _) (.hyp (Or.inl rfl))
    exact .impE (add (.conjL hk) _) hb
  · apply Derives.impI
    exact intro_substituted bound w r s a b c d n q (add hm _) (.impE (add (.conjR hk) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.SyntaxMixedTermKnown
