import PPAC.Migration.Internal.PacketReaderCodedTransport

/-! Every actual source-state code normalizes the complete eight-field coded transition block. -/
namespace PPAC.Migration.Internal.PacketReaderCodedNormalize
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStateSyntax PacketReaderCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code w l v s a n)) :
    Derives Γ ((step w B z o n r).iff (nextAt w B z o l v s a r)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := step w B z o n r
    let R := stepBody w B z o n r
    let Δ := Context.add R (raisedContext 8 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 8 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ8 := HornBinderRules.zf_body 8 (ZFContext.add hZ H) R
    have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 (add hw H) R)
    have hc8 := of_eq (code_rename w l v s a n (old 8)) (HornBinderRules.under_body 8 (add hc H) R)
    have he := PacketReaderStateCode.fields_unique hZ8 _ _ _ _ _ _ _ _ _ _ hw8 (.conjL hR) hc8
    have ha := PacketReaderCodedTransport.align_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he (.conjR (.conjR hR))
    exact of_eq (nextAt_rename w B z o l v s a r (old 8)).symm
      (intro_next _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL (.conjR hR)) ha)
  · apply Derives.impI
    let H := nextAt w B z o l v s a r
    let R := nextBody w B z o l v s a r
    let Δ := Context.add R (raisedContext 4 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 4 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hc4 := of_eq (code_rename w l v s a n (old 4)) (HornBinderRules.under_body 4 (add hc H) R)
    exact of_eq (step_rename w B z o n r (old 4)).symm
      (intro_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc4 (.conjL hR) (.conjR hR))

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (step w B z o n r)) : Derives Γ ((Formula.mem n w).conj (.mem r w)) := by
  let R := stepBody w B z o n r
  let Δ := Context.add R (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 R _ ht
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ8 := HornBinderRules.zf_body 8 hZ R
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw R)
  exact .conjI (PacketReaderStateCode.range hZ8 _ _ _ _ _ _ hw8 (.conjL hR))
    (PacketReaderStateCode.range hZ8 _ _ _ _ _ _ hw8 (.conjL (.conjR hR)))

theorem carriers {m} {Γ : Context m} (w B z o n r : Fin m) (ht : Derives Γ (step w B z o n r)) :
    Derives Γ ((carrier w n).conj (carrier w r)) := by
  let R := stepBody w B z o n r
  let Δ := Context.add R (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 R _ ht
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hn := intro_carrier _ _ _ _ _ _ (.conjL hR)
  have hr := intro_carrier _ _ _ _ _ _ (.conjL (.conjR hR))
  exact of_eq (by simp only [Formula.rename,carrier_rename]) (.conjI hn hr)

end PPAC.Migration.Internal.PacketReaderCodedNormalize
