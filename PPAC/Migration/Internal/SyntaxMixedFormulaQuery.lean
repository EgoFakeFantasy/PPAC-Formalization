import PPAC.Migration.Internal.SyntaxMixedFormulaQuerySyntax

/-! 混合状态在原完整历史图上的精确读取；只有实际对象边和状态成员，没有宿主选择函数。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaQuery
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxMixedFormulaStateSyntax SyntaxMixedFormulaQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem contains_legal {m} {Γ : Context m} (w v r s a b c d q : Fin m)
    (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (legal w r s a b c d q) := by
  let B := (Formula.mem (Fin.last m) v.castSucc).conj
    (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (legal_rename w r s a b c d q Fin.castSucc).symm (.conjR (.conjR hB))

theorem read_legal {m} {Γ : Context m} (w h x r s a b c d q : Fin m)
    (hr : Derives Γ (read w h x r s a b c d q)) : Derives Γ (legal w r s a b c d q) := by
  let B := (edge h.castSucc x.castSucc (Fin.last m)).conj
    (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (legal_rename w r s a b c d q Fin.castSucc).symm
    (contains_legal _ _ _ _ _ _ _ _ _ (.conjR hB))

theorem contains_at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v r s a b c d q t : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (state w r s a b c d q t)) :
    Derives Γ ((contains w v r s a b c d q).iff (.mem t v)) := by
  apply Derives.conjI
  · apply Derives.impI
    let C := contains w v r s a b c d q
    let Ξ := Context.add C Γ
    let B := (Formula.mem (Fin.last m) v.castSucc).conj
      (state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw C) B)
    have ht1 := of_eq (state_rename w r s a b c d q t Fin.castSucc) (under (add ht C) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := SyntaxMixedFormulaState.unique (ZFContext.under (ZFContext.add hZ C) B)
      w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m) t.castSucc
      hw1 (.conjL (.conjR hB)) (.conjL ht1)
    exact mem_subst he (.conjL hB)
  · apply Derives.impI
    exact intro_contains w v r s a b c d q t (.hyp (Or.inl rfl)) (add ht _)

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h D x v r s a b c d q : Fin m)
    (hf : Derives Γ (functionOn h D)) (hv : Derives Γ (edge h x v)) :
    Derives Γ ((read w h x r s a b c d q).iff (contains w v r s a b c d q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let C := read w h x r s a b c d q
    let Ξ := Context.add C Γ
    let B := (edge h.castSucc x.castSucc (Fin.last m)).conj
      (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc)
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hf1 := of_eq (functionOn_rename h D Fin.castSucc) (under (add hf C) B)
    have hv1 := of_eq (edge_rename h x v Fin.castSucc) (under (add hv C) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic (ZFContext.under (ZFContext.add hZ C) B)).base.extensionality
      hf1 (.conjL hB) hv1
    have ho := contains_subst_set _ _ _ _ _ _ _ _ _ _ he (.conjR hB)
    exact of_eq (contains_rename w v r s a b c d q Fin.castSucc).symm ho
  · apply Derives.impI
    exact intro_read w h x r s a b c d q v (add hv _) (.hyp (Or.inl rfl))

theorem at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h D x v r s a b c d q t : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn h D)) (hv : Derives Γ (edge h x v))
    (ht : Derives Γ (state w r s a b c d q t)) :
    Derives Γ ((read w h x r s a b c d q).iff (.mem t v)) := by
  have h1 := at_value hZ w h D x v r s a b c d q hf hv
  have h2 := contains_at_state hZ w v r s a b c d q t hw ht
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL h2) _) (.impE (add (.conjL h1) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR h1) _) (.impE (add (.conjR h2) _) (.hyp (Or.inl rfl)))

theorem advanced_input {m} {Γ : Context m} (w h x r s a b c d q : Fin m)
    (ha : Derives Γ (advanced w h x r s a b c d q)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d r s) := by
  let B := advancedBody w h x r s a b c d q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_advanced w h x r s a b c d q _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjL hB)
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) (.conjL hi)

theorem advanced_output_natural {m} {Γ : Context m} (w h x r s a b c d q : Fin m)
    (ha : Derives Γ (advanced w h x r s a b c d q)) : Derives Γ (.mem q w) := by
  let B := advancedBody w h x r s a b c d q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_advanced w h x r s a b c d q _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hl := read_legal w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjR hB)
  exact .conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (.conjR hl))

end PPAC.Migration.Internal.SyntaxMixedFormulaQuery
