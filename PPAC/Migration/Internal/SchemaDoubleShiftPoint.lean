import PPAC.Migration.Internal.SchemaDoubleShiftSyntax

/-! Exact edges on all internal candidates, including rejection outside the domain. -/
namespace PPAC.Migration.Internal.SchemaDoubleShiftPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SchemaDoubleShiftSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem composite_value_iff {m} {Γ : Context m} (w n b c r t i j : Fin m)
    (hr : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w n b r))
    (ht : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w b c t)) :
    Derives Γ ((SyntaxComposeSyntax.value r t i j).iff ((Formula.mem i n).conj (displacement i j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := SyntaxComposeSyntax.value r t i j
    let B := (edge r.castSucc i.castSucc (Fin.last m)).conj (edge t.castSucc (Fin.last m) j.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w n b r Fin.castSucc) (under (add hr E) B)
    have ht1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w b c t Fin.castSucc) (under (add ht E) B)
    have he0 := SyntaxFreeShiftGraph.edge_iff n.castSucc r.castSucc i.castSucc (Fin.last m)
      (SyntaxFreeShiftGraph.to_graph w.castSucc n.castSucc b.castSucc r.castSucc hr1)
    have he1 := SyntaxFreeShiftGraph.edge_iff b.castSucc t.castSucc (Fin.last m) j.castSucc
      (SyntaxFreeShiftGraph.to_graph w.castSucc b.castSucc c.castSucc t.castSucc ht1)
    have h0 := Derives.impE (.conjL he0) (.conjL hB)
    have h1 := Derives.impE (.conjL he1) (.conjR hB)
    exact of_eq (by simp only [Formula.raise, Formula.rename, displacement_rename])
      (.conjI (.conjL h0) (intro_displacement i.castSucc j.castSucc (Fin.last m) (.conjR h0) (.conjR h1)))
  · apply Derives.impI
    let E := (Formula.mem i n).conj (displacement i j)
    let B := (successor (Fin.last m) i.castSucc).conj (successor j.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.exE (p := B) (Derives.conjR hE)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hi1 : Derives Δ (.mem i.castSucc n.castSucc) := under (.conjL hE) B
    have hr1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w n b r Fin.castSucc) (under (add hr E) B)
    have ht1 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w b c t Fin.castSucc) (under (add ht E) B)
    have he0 := SyntaxFreeShiftGraph.edge_iff n.castSucc r.castSucc i.castSucc (Fin.last m)
      (SyntaxFreeShiftGraph.to_graph w.castSucc n.castSucc b.castSucc r.castSucc hr1)
    have hx := Derives.impE (.conjR he0) (.conjI hi1 (.conjL hB))
    have hk := SyntaxIndexMapSyntax.edge_target w.castSucc r.castSucc n.castSucc b.castSucc i.castSucc (Fin.last m) (.conjL (.conjR hr1)) hx
    have he1 := SyntaxFreeShiftGraph.edge_iff b.castSucc t.castSucc (Fin.last m) j.castSucc
      (SyntaxFreeShiftGraph.to_graph w.castSucc b.castSucc c.castSucc t.castSucc ht1)
    have hz := Derives.impE (.conjR he1) (.conjI hk (.conjR hB))
    exact of_eq (SyntaxComposeSyntax.value_rename r t i j Fin.castSucc).symm
      (SyntaxComposeSyntax.intro_value r.castSucc t.castSucc i.castSucc j.castSucc (Fin.last m) hx hz)

theorem matrix_edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c g i j : Fin m) (env : Fin 2 → Fin m)
    (hm : Derives Γ (SchemaDoubleShiftSyntax.matrix w n b c g env)) :
    Derives Γ ((edge g i j).iff ((Formula.mem i n).conj (displacement i j))) := by
  have hc := SyntaxComposeGraph.edge_iff hZ w (env 0) (env 1) n b c g i j (.conjR (.conjR hm))
  have hd := composite_value_iff w n b c (env 0) (env 1) i j (.conjL hm) (.conjL (.conjR hm))
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hd) _) (.impE (add (.conjL hc) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hc) _) (.impE (add (.conjR hd) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.SchemaDoubleShiftPoint
