import PPAC.Migration.Internal.PacketStructureRootCons

/-! The original packet head orders byte-output before tree-input; both are aligned without swapping them. -/
namespace PPAC.Migration.Internal.PacketStructureRootPacket
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureRootSyntax PacketStructureRootTransport
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V a n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (packetRow w a n r))
    (ho : Derives Γ (PacketStructureApplicationSyntax.outcome .packet w V r)) : Derives Γ (packetCase w V a n) := by
  let L := PacketStructureRootWitness.packetWitness w V r
  let Δ := Context.add L (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ (of_eq (PacketStructureRootWitness.actual_packet_witness w V r) ho)
  have hZ4 := HornBinderRules.zf_body 4 hZ L
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw L)
  have hr4 := of_eq (packetRow_rename w a n r (old 4)) (HornBinderRules.under_body 4 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR hL
  have he (i : Fin 2) := SyntaxNodeInjective.constructor_input_eq hZ4 2 5 5 (old 4 w)
    (SyntaxAtomSyntax.two (slot 4 1) (slot 4 0)) (SyntaxAtomSyntax.two (old 4 a) (old 4 n))
    (old 4 r) i hw4 (.conjL hA) hr4
  have hp := Derives.conjR hA
  have ha := PacketTokenRootTransport.entry_third 1 (old 4 w) (old 4 V) (slot 4 3) (slot 4 2) (slot 4 1) (old 4 a) (he 0) (.conjL hp)
  have ht := tree_input (old 4 w) (old 4 V) (slot 4 0) (slot 4 3) (slot 4 2) (old 4 n) (he 1) (.conjR hp)
  exact of_eq (packetCase_rename w V a n (old 4)).symm
    (PacketStructureRootSyntax.intro_packet (old 4 w) (old 4 V) (old 4 a) (old 4 n) (slot 4 3) (slot 4 2) (.conjL hL) ha ht)

theorem backward {m} {Γ : Context m} (w V a n r : Fin m) (hr : Derives Γ (packetRow w a n r))
    (hc : Derives Γ (packetCase w V a n)) : Derives Γ (PacketStructureApplicationSyntax.outcome .packet w V r) := by
  let L := packetCaseBody w V a n
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hc
  have hr2 := of_eq (packetRow_rename w a n r (old 2)) (HornBinderRules.under_body 2 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  let env := SyntaxAtomSyntax.three (old 2 n) (old 2 a) (slot 2 1)
  have ha : Derives Δ (packetAt (old 2 w) (old 2 V) (old 2 r) (slot 2 0) env) := .conjI hr2 (.conjR hL)
  have hl := PacketStructureLocalSyntax.intro_packet (old 2 w) (old 2 V) (old 2 r) (slot 2 0) env (.conjL hL) ha
  exact of_eq (PacketStructureApplicationSyntax.outcome_rename .packet w V r (old 2)).symm
    (PacketStructureApplicationSyntax.intro_outcome .packet (old 2 w) (old 2 V) (old 2 r) env hl)

theorem root_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V a n r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (packetRow w a n r)) :
    Derives Γ ((PacketStructureApplicationSyntax.outcome .packet w V r).iff (packetCase w V a n)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w V a n r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w V a n r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureRootPacket
