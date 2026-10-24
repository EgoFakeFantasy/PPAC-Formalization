import PPAC.Migration.Internal.PacketStructureSearchBounds

/-! All original assignment guards are derived, so every complete unbounded structural outcome reconstructs its original bounded application. -/
namespace PPAC.Migration.Internal.PacketStructureSearchApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (ho : Derives Γ (outcome b w V r)) :
    Derives Γ (HornApplicationSyntax.application (rule b) w r V) := by
  let L := outcomeBody b w V r
  let Δ := Context.add L (raisedContext (rule b).arity Γ)
  apply HornBinderRules.eliminate_many (rule b).arity L _ ho
  have hZk := HornBinderRules.zf_body (rule b).arity hZ L
  have hwk := of_eq (omega_rename w (old (rule b).arity)) (HornBinderRules.under_body (rule b).arity hw L)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old (rule b).arity)) (HornBinderRules.under_body (rule b).arity hv L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hn := PacketStructureSearchEnvironment.local_natural hZk b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) hwk hL
  have hb := PacketStructureSearchBounds.local_bounds hZk b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) hwk hvk hL
  have hm := PacketStructureSearchHead.matrix_of_local hZk b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) hwk hL
  exact of_eq (HornApplicationSyntax.application_rename (rule b) w r V (old (rule b).arity)).symm
    (HornApplicationRules.intro_application (rule b) (old (rule b).arity w) (old (rule b).arity r) (old (rule b).arity V) (slot (rule b).arity) hn hb hm)

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (rule b) w r V).iff (outcome b w V r)) := by
  apply Derives.conjI
  · exact .impI (PacketStructureApplication.forward (ZFContext.add hZ _) b w V r (add hw _) (.hyp (Or.inl rfl)))
  · exact .impI (backward (ZFContext.add hZ _) b w V r (add hw _) (add hv _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketStructureSearchApplication
