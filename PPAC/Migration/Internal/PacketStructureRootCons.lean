import PPAC.Migration.Internal.PacketStructureRootNil

/-! All eight original Cons witnesses align with the specified forest and its actual length, tail and output. -/
namespace PPAC.Migration.Internal.PacketStructureRootCons
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureRootSyntax PacketStructureRootTransport
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n l t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (forestRow w n l t a r))
    (ho : Derives Γ (PacketStructureApplicationSyntax.outcome .cons w V r)) : Derives Γ (consCase w V n l t a) := by
  let L := PacketStructureRootWitness.consWitness w V r
  let Δ := Context.add L (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 L _ (of_eq (PacketStructureRootWitness.actual_cons_witness w V r) ho)
  have hZ8 := HornBinderRules.zf_body 8 hZ L
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw L)
  have hr8 := of_eq (forestRow_rename w n l t a r (old 8)) (HornBinderRules.under_body 8 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR (.conjR hL)
  have he (i : Fin 4) := SyntaxNodeInjective.constructor_input_eq hZ8 4 4 4 (old 8 w)
    (four (slot 8 6) (slot 8 7) (slot 8 3) (slot 8 4)) (four (old 8 n) (old 8 l) (old 8 t) (old 8 a))
    (old 8 r) i hw8 (.conjL hA) hr8
  have hc := HornExprStructural.cons_output_subst (old 8 w) (slot 8 0) (slot 8 1) (slot 8 6) (old 8 n) (he 0) (.conjL hL)
  have hs := IterationExtensionAlgebra.successor_subst_target (slot 8 7) (old 8 l) (slot 8 2) (he 1) (.conjL (.conjR hL))
  have hp := Derives.conjR hA
  have hf := forest_tail (old 8 w) (old 8 V) (slot 8 1) (slot 8 2) (slot 8 3) (slot 8 5) (old 8 t) (he 2) (.conjL hp)
  have ht := tree_output (old 8 w) (old 8 V) (slot 8 0) (slot 8 5) (slot 8 4) (old 8 a) (he 3) (.conjR hp)
  exact of_eq (consCase_rename w V n l t a (old 8)).symm
    (PacketStructureRootSyntax.intro_cons (old 8 w) (old 8 V) (old 8 n) (old 8 l) (old 8 t) (old 8 a)
      (slot 8 0) (slot 8 1) (slot 8 2) (slot 8 5) hc hs hf ht)

theorem backward {m} {Γ : Context m} (w V n l t a r : Fin m) (hr : Derives Γ (forestRow w n l t a r))
    (hc : Derives Γ (consCase w V n l t a)) : Derives Γ (PacketStructureApplicationSyntax.outcome .cons w V r) := by
  let L := consCaseBody w V n l t a
  let Δ := Context.add L (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ hc
  have hr4 := of_eq (forestRow_rename w n l t a r (old 4)) (HornBinderRules.under_body 4 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  let env : Fin 6 → Fin (m+4) := Fin.cases (slot 4 0) (Fin.cases (slot 4 1) (Fin.cases (slot 4 2) (Fin.cases (old 4 t)
    (Fin.cases (old 4 a) (Fin.cases (slot 4 3) Fin.elim0)))))
  have ha : Derives Δ (consAt (old 4 w) (old 4 V) (old 4 r) (old 4 n) (old 4 l) env) := .conjI hr4 (.conjR (.conjR hL))
  have hl := PacketStructureLocalSyntax.intro_cons (old 4 w) (old 4 V) (old 4 r) (old 4 n) (old 4 l) env (.conjL hL) (.conjL (.conjR hL)) ha
  exact of_eq (PacketStructureApplicationSyntax.outcome_rename .cons w V r (old 4)).symm
    (PacketStructureApplicationSyntax.intro_outcome .cons (old 4 w) (old 4 V) (old 4 r) env hl)

theorem root_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n l t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (forestRow w n l t a r)) :
    Derives Γ ((PacketStructureApplicationSyntax.outcome .cons w V r).iff (consCase w V n l t a)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w V n l t a r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w V n l t a r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureRootCons
