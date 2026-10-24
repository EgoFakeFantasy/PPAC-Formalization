import PPAC.Migration.Internal.PacketBytesDecomposition

/-! Both directions for the independent concrete fold graph hold on all internal candidates. -/
namespace PPAC.Migration.Internal.PacketBytesRecursionEquation
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (consCase w C n t a)) : Derives Γ (foldAt w C n t a) := by
  let R := consBody w C n t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (foldAt_rename w C n t a (old 3)).symm
    (PacketBytesTraceAppend.cons_fold hZ3 (old 3 w) (old 3 C) (slot 3 1) (old 3 t) (slot 3 2) (slot 3 0) (old 3 n) (old 3 a)
      hw3 (.conjL (.conjR hR)) (.conjL hR) (.conjR (.conjR hR)))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (caseAt w C n t a)) : Derives Γ (foldAt w C n t a) := by
  apply Derives.disjE hc
  · have hN : Derives (Context.add (nilCase w n t a) Γ) (nilCase w n t a) := .hyp (Or.inl rfl)
    have hf := PacketBytesTraceBase.nil_fold (ZFContext.add hZ _) w C n t (add hw _) (.conjL hN) (.conjL (.conjR hN))
    exact PacketBytesTraceTransport.output_subst w C n t t a (.conjR (.conjR hN)) hf
  · exact cons_backward (ZFContext.add hZ _) w C n t a (add hw _) (.hyp (Or.inl rfl))

theorem fold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((foldAt w C n t a).iff (caseAt w C n t a)) :=
  .conjI (.impI (PacketBytesDecomposition.fold_forward (ZFContext.add hZ _) w C n t a (add hw _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w C n t a (add hw _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketBytesRecursionEquation
