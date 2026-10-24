import PPAC.Migration.Internal.SchemaIndexFacts

/-! Exact parameter tails, with real successor witnesses and arbitrary internal indices. -/
namespace PPAC.Migration.Internal.SchemaIndexTail
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem shift_at_source {m} {Γ : Context m} (w n b r i j : Fin m)
    (hr : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w n b r)) (hi : Derives Γ (.mem i n)) :
    Derives Γ ((edge r i j).iff (successor j i)) := by
  have he := SyntaxFreeShiftGraph.edge_iff n r i j (SyntaxFreeShiftGraph.to_graph w n b r hr)
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))

theorem double_at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b c r i j : Fin m)
    (hr : Derives Γ (SchemaDoubleShiftSyntax.map w n b c r)) (hi : Derives Γ (.mem i n)) :
    Derives Γ ((edge r i j).iff (SchemaDoubleShiftSyntax.displacement i j)) := by
  have he := SchemaDoubleShiftGraph.edge_iff hZ w n b c r i j hr
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))

theorem separation_matrix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (g : Fin m) (env : Fin 2 → Fin m) (i I j J : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SchemaIndexSyntax.matrix 0 w n scopes g env)) (hi : Derives Γ (.mem i n))
    (hI : Derives Γ (successor I i)) (hJ : Derives Γ (successor J j)) :
    Derives Γ ((edge g I J).iff (SchemaDoubleShiftSyntax.displacement i j)) := by
  have h0 := SyntaxIndexLiftEdges.successor_iff hZ w (env 0) n (scopes 1) (scopes 0) (scopes 2) g I J i j
    hw (.conjR (.conjR hm)) hi hI hJ
  have h1 := double_at_source hZ w n (scopes 0) (scopes 1) (env 0) i j (.conjL hm) hi
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL h1) _) (.impE (add (.conjL h0) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR h0) _) (.impE (add (.conjR h1) _) (.hyp (Or.inl rfl)))

theorem collection_matrix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (image : Bool) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m) (i u I j v J : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes))
    (hm : Derives Γ (SchemaIndexSyntax.matrix (if image then 2 else 1) w n scopes g env))
    (hi : Derives Γ (.mem i n)) (hu : Derives Γ (successor u i)) (hI : Derives Γ (successor I u))
    (hv : Derives Γ (successor v j)) (hJ : Derives Γ (successor J v)) :
    Derives Γ ((edge g I J).iff (if image then SchemaDoubleShiftSyntax.displacement i j else successor j i)) := by
  have hiW := StructuralListTraceOrder.member_member hZ w i n hw hn hi
  have huS := SyntaxIndexLiftOrder.successor_member hZ w i n u (scopes 0) hw hiW hn hi hu (.conjL hc)
  cases image with
  | false =>
    have h0 := SyntaxIndexLiftEdges.successor_iff hZ w (env 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) g I J u v hw (.conjR (.conjR hm)) huS hI hJ
    have h1 := SyntaxIndexLiftEdges.successor_iff hZ w (env 0) n (scopes 0) (scopes 0) (scopes 1) (env 1) u v i j hw (.conjL (.conjR hm)) hi hu hv
    have h2 := shift_at_source w n (scopes 0) (env 0) i j (.conjL hm) hi
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjL h2) _) (.impE (add (.conjL h1) _) (.impE (add (.conjL h0) _) (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .impE (add (.conjR h0) _) (.impE (add (.conjR h1) _) (.impE (add (.conjR h2) _) (.hyp (Or.inl rfl))))
  | true =>
    have h0 := SyntaxIndexLiftEdges.successor_iff hZ w (env 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) g I J u v hw (.conjR (.conjR hm)) huS hI hJ
    have h1 := SyntaxIndexLiftEdges.successor_iff hZ w (env 0) n (scopes 1) (scopes 0) (scopes 2) (env 1) u v i j hw (.conjL (.conjR hm)) hi hu hv
    have h2 := double_at_source hZ w n (scopes 0) (scopes 1) (env 0) i j (.conjL hm) hi
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjL h2) _) (.impE (add (.conjL h1) _) (.impE (add (.conjL h0) _) (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .impE (add (.conjR h0) _) (.impE (add (.conjR h1) _) (.impE (add (.conjR h2) _) (.hyp (Or.inl rfl))))

theorem separation_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (g i I j J : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (state 0 w n scopes g))
    (hi : Derives Γ (.mem i n)) (hI : Derives Γ (successor I i)) (hJ : Derives Γ (successor J j)) :
    Derives Γ ((edge g I J).iff (SchemaDoubleShiftSyntax.displacement i j)) := by
  let B := body 0 w n scopes g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (Derives.conjR hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hi2 : Derives Δ (.mem (old 2 i) (old 2 n)) := HornBinderRules.under_body 2 hi B
  have hI2 := of_eq (successor_rename I i (old 2)) (HornBinderRules.under_body 2 hI B)
  have hJ2 := of_eq (successor_rename J j (old 2)) (HornBinderRules.under_body 2 hJ B)
  have ho := separation_matrix (HornBinderRules.zf_body 2 hZ B) (old 2 w) (old 2 n) (fun k => old 2 (scopes k)) (old 2 g) (slot 2)
    (old 2 i) (old 2 I) (old 2 j) (old 2 J) hw2 hB hi2 hI2 hJ2
  exact of_eq (by simp only [Formula.iff, Formula.rename, edge_rename, SchemaDoubleShiftSyntax.displacement_rename]) ho

theorem collection_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (image : Bool) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g i u I j v J : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (state (if image then 2 else 1) w n scopes g)) (hi : Derives Γ (.mem i n))
    (hu : Derives Γ (successor u i)) (hI : Derives Γ (successor I u)) (hv : Derives Γ (successor v j)) (hJ : Derives Γ (successor J v)) :
    Derives Γ ((edge g I J).iff (if image then SchemaDoubleShiftSyntax.displacement i j else successor j i)) := by
  let B := body (if image then 2 else 1) w n scopes g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (Derives.conjR hs)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (.mem (old 2 n) (old 2 w)) := HornBinderRules.under_body 2 hn B
  have hi2 : Derives Δ (.mem (old 2 i) (old 2 n)) := HornBinderRules.under_body 2 hi B
  have hc2 := of_eq (chain_rename n scopes (old 2)) (HornBinderRules.under_body 2 (.conjL hs) B)
  have hu2 := of_eq (successor_rename u i (old 2)) (HornBinderRules.under_body 2 hu B)
  have hI2 := of_eq (successor_rename I u (old 2)) (HornBinderRules.under_body 2 hI B)
  have hv2 := of_eq (successor_rename v j (old 2)) (HornBinderRules.under_body 2 hv B)
  have hJ2 := of_eq (successor_rename J v (old 2)) (HornBinderRules.under_body 2 hJ B)
  have ho := collection_matrix (HornBinderRules.zf_body 2 hZ B) image (old 2 w) (old 2 n) (fun k => old 2 (scopes k)) (old 2 g) (slot 2)
    (old 2 i) (old 2 u) (old 2 I) (old 2 j) (old 2 v) (old 2 J) hw2 hn2 hc2 hB hi2 hu2 hI2 hv2 hJ2
  exact of_eq (by
    cases image with
    | false => simp only [Bool.false_eq_true, if_false, Formula.iff, Formula.rename, edge_rename, successor_rename]
    | true => simp only [if_true, Formula.iff, Formula.rename, edge_rename, SchemaDoubleShiftSyntax.displacement_rename]) ho

end PPAC.Migration.Internal.SchemaIndexTail
