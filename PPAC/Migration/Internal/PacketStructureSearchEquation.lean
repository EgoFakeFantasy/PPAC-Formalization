import PPAC.Migration.Internal.PacketStructureSearchApplication

/-! The actual root condition is now equivalent to the full normalized structural cases in the canonical accepting set. -/
namespace PPAC.Migration.Internal.PacketStructureSearchEquation
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureSyntax PacketStructureDispatchData

theorem applications_iff_outcomes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketStructureDispatch.applications f w V r).iff (PacketStructureDispatch.results false f w V r)) := by
  cases f with
  | tree => exact PacketStructureSearchApplication.application_iff hZ .tree w V r hw hv
  | forest =>
    exact SyntaxTypeLocalTransfer.disj_congr (PacketStructureSearchApplication.application_iff hZ .nil w V r hw hv)
      (PacketStructureSearchApplication.application_iff hZ .cons w V r hw hv)
  | packet => exact PacketStructureSearchApplication.application_iff hZ .packet w V r hw hv

theorem condition_iff_criterion {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hr : Derives Γ (row (width f) (tag f) w xs r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (PacketStructureRootSyntax.criterion f w V xs)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.unfold_iff hZ w V r hw hv)
    (SyntaxTypeLocalTransfer.iff_trans (PacketStructureDispatch.step_iff_applications hZ f w V r xs hw hr)
      (SyntaxTypeLocalTransfer.iff_trans (applications_iff_outcomes hZ f w V r hw hv) (PacketStructureRootEquation.outcomes_iff hZ f w V r xs hw hr)))

end PPAC.Migration.Internal.PacketStructureSearchEquation
