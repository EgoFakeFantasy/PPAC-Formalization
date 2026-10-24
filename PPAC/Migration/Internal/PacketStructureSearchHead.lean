import PPAC.Migration.Internal.PacketStructureSearchArithmetic

/-! Every variable actually present in the unchanged original head is below its real root row. -/
namespace PPAC.Migration.Internal.PacketStructureSearchHead
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketStructureApplicationSyntax

theorem matrix_of_local {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (localCase b w V r env)) : Derives Γ (HornRuleSyntax.matrix (rule b) w r V env) :=
  .impE (.conjR (PacketStructureApplication.local_iff hZ b w V r env hw (PacketStructureSearchEnvironment.local_natural hZ b w V r env hw hl))) hl

theorem root_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (localCase b w V r env)) : Derives Γ (.mem r w) :=
  HornExprRange.range hZ (rule b).head w r env hw (PacketStructureSearchEnvironment.local_natural hZ b w V r env hw hl)
    (.conjL (matrix_of_local hZ b w V r env hw hl))

theorem variable_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (i : Fin (rule b).arity)
    (hi : i ∈ (rule b).head.variables) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (localCase b w V r env)) : Derives Γ (NaturalAdditionBounds.below (env i) r) :=
  HornExprBounds.variable_bound hZ (rule b).head i hi w r env hw (PacketStructureSearchEnvironment.local_natural hZ b w V r env hw hl)
    (.conjL (matrix_of_local hZ b w V r env hw hl))

end PPAC.Migration.Internal.PacketStructureSearchHead
