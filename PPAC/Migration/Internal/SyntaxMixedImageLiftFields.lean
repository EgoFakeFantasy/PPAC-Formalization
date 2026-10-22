import PPAC.Migration.Internal.SyntaxMixedImageLiftExistence

/-! 混合binder表的精确目标类型及新bound0、旧bound后继、free保持的原对象端点律。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageLiftFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedImageLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_maps {m} {Γ : Context m} (w R S r s a b c d A C n k h : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) :
    Derives Γ (SyntaxTermImageSyntax.maps w k h A b C d) := by
  let B := body w R S r s a b c d A C n k h
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := SyntaxTermImagePushBoth.target_maps w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc d.castSucc r.castSucc s.castSucc a.castSucc b.castSucc (Fin.last m) h.castSucc (.conjL hB)
  have ht : Derives Δ (SyntaxTermImageSyntax.maps w.castSucc k.castSucc h.castSucc A.castSucc b.castSucc C.castSucc d.castSucc) :=
    .conjI (.conjL (.conjR (.conjR (.conjR (.conjR hB)))) ) (.conjR hm)
  exact of_eq (SyntaxTermImageSyntax.maps_rename w k h A b C d Fin.castSucc).symm ht

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d A C n k h z q : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((edge k z q).iff (Formula.equal q n)) := by
  let B := body w R S r s a b c d A C n k h
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have ho := SyntaxTermImagePrefixGraph.zero_iff hZ1 w.castSucc (Fin.last m) a.castSucc C.castSucc d.castSucc n.castSucc A.castSucc k.castSucc z.castSucc q.castSucc hw1 (.conjR hB) hz1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename]) ho

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d A C n k h i j t q : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) (hw : Derives Γ (omega w)) (hj : Derives Γ (.mem j a)) (hi : Derives Γ (successor i j)) (ht : Derives Γ (edge r j t)) :
    Derives Γ ((edge k i q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q)) := by
  let B := body w R S r s a b c d A C n k h
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hj1 : Derives Δ (.mem j.castSucc a.castSucc) := under hj B
  have hi1 : Derives Δ (successor i.castSucc j.castSucc) := of_eq (successor_rename i j Fin.castSucc) (under hi B)
  have ht1 : Derives Δ (edge r.castSucc j.castSucc t.castSucc) := of_eq (edge_rename r j t Fin.castSucc) (under ht B)
  have hp := SyntaxTermImagePrefixGraph.successor_iff hZ1 w.castSucc (Fin.last m) a.castSucc C.castSucc d.castSucc n.castSucc A.castSucc k.castSucc i.castSucc q.castSucc j.castSucc hw1 (.conjR hB) hj1 hi1
  have hr := SyntaxTermImagePushGraph.at_value hZ1 w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc d.castSucc r.castSucc a.castSucc (Fin.last m) j.castSucc t.castSucc q.castSucc (.conjL (.conjL hB)) ht1
  have ho : Derives Δ ((edge k.castSucc i.castSucc q.castSucc).iff (SyntaxRenameTermSyntax.renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc d.castSucc t.castSucc q.castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjL hr) _) (.impE (add (.conjL hp) _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .impE (add (.conjR hp) _) (.impE (add (.conjR hr) _) (.hyp (Or.inl rfl)))
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d A C n k h j t q : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) (ht : Derives Γ (edge s j t)) :
    Derives Γ ((edge h j q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q)) := by
  let B := body w R S r s a b c d A C n k h
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have ht1 : Derives Δ (edge s.castSucc j.castSucc t.castSucc) := of_eq (edge_rename s j t Fin.castSucc) (under ht B)
  have ho := SyntaxTermImagePushGraph.at_value hZ1 w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc d.castSucc s.castSucc b.castSucc h.castSucc j.castSucc t.castSucc q.castSucc (.conjR (.conjL hB)) ht1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, edge_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem source_inputs {m} {Γ : Context m} (w R S r s a b c d A C n k h : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) :
    Derives Γ ((SyntaxTermImageSyntax.maps w r s a b c d).conj (successor A a)) := by
  let B := body w R S r s a b c d A C n k h
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi : Derives Δ ((SyntaxTermImageSyntax.maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc).conj (successor A.castSucc a.castSucc)) :=
    .conjI (.conjI (.conjL (.conjL (.conjL hB))) (.conjL (.conjR (.conjL hB)))) (.conjL (.conjR (.conjR (.conjR hB))))
  exact of_eq (by simp only [Formula.raise, Formula.rename, SyntaxTermImageSyntax.maps_rename, successor_rename]) hi

end PPAC.Migration.Internal.SyntaxMixedImageLiftFields
