import PPAC.Migration.Internal.PacketStructureRootTree

/-! Actual Nil is the successor of internal zero, and both original tail fields coincide. -/
namespace PPAC.Migration.Internal.PacketStructureRootNil
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureRootSyntax PacketStructureRootTransport
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n l t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (forestRow w n l t a r))
    (ho : Derives Γ (PacketStructureApplicationSyntax.outcome .nil w V r)) : Derives Γ (nilCase n l t a) := by
  let L := PacketStructureRootWitness.nilWitness w V r
  let Δ := Context.add L (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 L _ (of_eq (PacketStructureRootWitness.actual_nil_witness w V r) ho)
  have hZ3 := HornBinderRules.zf_body 3 hZ L
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw L)
  have hr3 := of_eq (forestRow_rename w n l t a r (old 3)) (HornBinderRules.under_body 3 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have he (i : Fin 4) := SyntaxNodeInjective.constructor_input_eq hZ3 4 4 4 (old 3 w)
    (four (slot 3 2) (slot 3 1) (slot 3 0) (slot 3 0)) (four (old 3 n) (old 3 l) (old 3 t) (old 3 a))
    (old 3 r) i hw3 (.conjR (.conjR hL)) hr3
  have hz := empty_value (slot 3 1) (old 3 l) (he 1) (.conjL hL)
  have hs := GodelUnpairArithmetic.successor_base_subst (old 3 n) (slot 3 1) (old 3 l) (he 1)
    (IterationExtensionAlgebra.successor_subst_target (slot 3 2) (old 3 n) (slot 3 1) (he 0) (.conjL (.conjR hL)))
  have hta := eq_trans (eq_symm (he 2)) (he 3)
  exact of_eq (nilCase_rename n l t a (old 3)).symm (.conjI hz (.conjI hs hta))

theorem backward {m} {Γ : Context m} (w V n l t a r : Fin m) (hr : Derives Γ (forestRow w n l t a r))
    (hc : Derives Γ (nilCase n l t a)) : Derives Γ (PacketStructureApplicationSyntax.outcome .nil w V r) := by
  have hr0 := forest_row_output w n l t a r t (eq_symm (.conjR (.conjR hc))) hr
  have hl := PacketStructureLocalSyntax.intro_nil w V r l n (fun _ : Fin 1 => t) (.conjL hc) (.conjL (.conjR hc)) hr0
  exact PacketStructureApplicationSyntax.intro_outcome .nil w V r (fun _ : Fin 1 => t) hl

theorem root_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n l t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (forestRow w n l t a r)) :
    Derives Γ ((PacketStructureApplicationSyntax.outcome .nil w V r).iff (nilCase n l t a)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w V n l t a r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w V n l t a r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureRootNil
