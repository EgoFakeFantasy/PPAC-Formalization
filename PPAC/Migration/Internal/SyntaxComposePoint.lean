import PPAC.Migration.Internal.SyntaxComposeSyntax

/-! 复合值的实际中间值、定义域/值域和单值性；不假设内部图单射。 -/
namespace PPAC.Migration.Internal.SyntaxComposePoint
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxIndexMapSyntax SyntaxComposeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem source_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c i j : Fin m)
    (hr : Derives Γ (indexMap w r a c)) (hv : Derives Γ (value r t i j)) : Derives Γ (.mem i a) := by
  let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (edge t.castSucc (Fin.last m) j.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.edge_source (ZFContext.under hZ B) _ _ _ _ _ _ hr1 (.conjL hB)

theorem target_member {m} {Γ : Context m} (w r t c e i j : Fin m)
    (ht : Derives Γ (indexMap w t c e)) (hv : Derives Γ (value r t i j)) : Derives Γ (.mem j e) := by
  let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (edge t.castSucc (Fin.last m) j.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have ht1 : Derives Δ (indexMap w.castSucc t.castSucc c.castSucc e.castSucc) := of_eq (indexMap_rename w t c e Fin.castSucc) (under ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.edge_target _ _ _ _ _ _ ht1 (.conjR hB)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e i j l : Fin m)
    (hr : Derives Γ (indexMap w r a c)) (ht : Derives Γ (indexMap w t c e))
    (hj : Derives Γ (value r t i j)) (hl : Derives Γ (value r t i l)) : Derives Γ (.equal j l) := by
  let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (edge t.castSucc (Fin.last m) j.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hj
  have hl1 : Derives Ξ (value r.castSucc t.castSucc i.castSucc l.castSucc) := of_eq (value_rename r t i l Fin.castSucc) (under hl B)
  let C := (edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj (edge t.castSucc.castSucc (Fin.last (m+1)) l.castSucc.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hl1
  have hZ2 := ZFContext.under (ZFContext.under hZ B) C
  have hr2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (under (under hr B) C)
  have ht2 : Derives Δ (indexMap w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (under (under ht B) C)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hb2 : Derives Δ ((edge r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj (edge t.castSucc.castSucc (Fin.last m).castSucc j.castSucc.castSucc)) := of_eq (by simp only [B, Formula.raise, Formula.rename, edge_rename]) (under hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjL (.conjR hr2)) (.conjL hb2) (.conjL hC)
  have hj2 := IterationValues.edge_subst_input _ _ _ _ he (.conjR hb2)
  exact GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjL (.conjR ht2)) hj2 (.conjR hC)
end PPAC.Migration.Internal.SyntaxComposePoint
