import PPAC.Migration.Internal.SyntaxContextReadSyntax

/-! 读取实际历史集合值及真实后继bound；不把当前上下文冻结为单个布尔标志。 -/
namespace PPAC.Migration.Internal.SyntaxContextRead
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxContextReadSyntax SyntaxTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (h d x v b f : Fin m)
    (hf : Derives Γ (functionOn h d)) (hv : Derives Γ (edge h x v)) :
    Derives Γ ((read h x b f).iff (edge v b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := (edge h.castSucc x.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc)
    let Ξ := Context.add (read h x b f) Γ
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ (read h x b f)) R
    have hf1 : Derives Δ (functionOn h.castSucc d.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using under (add hf (read h x b f)) R
    have hv1 : Derives Δ (edge h.castSucc x.castSucc v.castSucc) := by
      simpa only [Formula.raise, edge_rename] using under (add hv (read h x b f)) R
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have he := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hf1 (.conjL hR) hv1
    have hout := IterationValueUniqueness.edge_subst_graph _ _ _ _ he (.conjR hR)
    simpa only [Formula.raise, edge_rename] using hout
  · apply Derives.impI
    exact intro_read _ _ _ _ v (add hv _) (.hyp (Or.inl rfl))

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (h x b f k : Fin m)
    (hk : Derives Γ (successor k b)) : Derives Γ ((advanced h x b f).iff (read h x k f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let K := (successor (Fin.last m) b.castSucc).conj (read h.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Ξ := Context.add (advanced h x b f) Γ
    let Δ := Context.add K (Context.image Formula.raise Ξ)
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ (advanced h x b f)) K
    have hk1 : Derives Δ (successor k.castSucc b.castSucc) := by
      simpa only [Formula.raise, successor_rename] using under (add hk (advanced h x b f)) K
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have he := InsertLogic.unique _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjL hK) hk1
    have hout := read_subst_bound _ _ _ _ _ he (.conjR hK)
    simpa only [Formula.raise, read_rename] using hout
  · apply Derives.impI
    exact intro_advanced _ _ _ _ k (add hk _) (.hyp (Or.inl rfl))

theorem successor_context {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (contexts w b f)) (hk : Derives Γ (successor k b)) :
    Derives Γ ((contexts w k f).conj (.mem b k)) := by
  exact .conjI (.conjI (OmegaStructureAlgebra.successor_member w k b (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hc) hk) (.conjR hc))
    (InsertLogic.new_member k b b hk)
end PPAC.Migration.Internal.SyntaxContextRead
