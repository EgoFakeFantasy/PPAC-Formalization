import PPAC.Migration.Internal.PacketStructureRootLawSyntax

/-! Final all-internal normalized forward recursion requires only omega and actual acceptance, with no traces or external witnesses. -/
namespace PPAC.Migration.Internal.PacketStructureRootLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData PacketStructureRootLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_root_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allRootLaw f w V) := by
  apply OriginalUniversalBlock.intro_many (width f+1)
  apply Derives.impI
  let H := row (width f) (tag f) (old (width f+1) w : Fin (m+(width f+1)))
    (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))
  have hwk := of_eq (omega_rename w (old (width f+1))) (HornBinderRules.under_body (width f+1) hw H)
  exact PacketStructureRootEquation.outcomes_iff (HornBinderRules.zf_body (width f+1) hZ H) f (old (width f+1) w) (old (width f+1) V)
    (slot (width f+1) (Fin.last (width f))) (fun i => slot (width f+1) i.castSucc) hwk (.hyp (Or.inl rfl))

theorem all_accepted_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allAcceptedLaw f w) := by
  apply OriginalUniversalBlock.intro_many (width f)
  apply Derives.impI
  let H := accepted (width f) (tag f) (old (width f) w : Fin (m+width f)) (slot (width f))
  have hwk := of_eq (omega_rename w (old (width f))) (HornBinderRules.under_body (width f) hw H)
  exact PacketStructureAcceptedForward.accepted_forward (HornBinderRules.zf_body (width f) hZ H) f (old (width f) w) (slot (width f)) hwk (.hyp (Or.inl rfl))

theorem tree_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (tree w n t a)) : Derives Γ (treeCase w n t a) :=
  PacketStructureAcceptedForward.accepted_forward hZ .tree w (SyntaxAtomSyntax.three n t a) hw ha

theorem forest_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (forest w n l t a)) :
    Derives Γ ((PacketStructureRootSyntax.nilCase n l t a).disj (consCase w n l t a)) :=
  PacketStructureAcceptedForward.accepted_forward hZ .forest w (four n l t a) hw ha

theorem packet_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (packet w a n)) : Derives Γ (packetCase w a n) :=
  PacketStructureAcceptedForward.accepted_forward hZ .packet w (SyntaxAtomSyntax.two a n) hw ha

theorem all_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allSystem w) :=
  .conjI (all_accepted_law hZ .tree w hw) (.conjI (all_accepted_law hZ .forest w hw) (all_accepted_law hZ .packet w hw))

end PPAC.Migration.Internal.PacketStructureRootLaws
