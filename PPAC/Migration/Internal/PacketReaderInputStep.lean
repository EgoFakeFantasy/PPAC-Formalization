import PPAC.Migration.Internal.PacketReaderInputNormalize

/-! Full-state steps preserve type and have four jointly unique outputs after eliminating the actual input decomposition. -/
namespace PPAC.Migration.Internal.PacketReaderInputStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (advance w B z o l v s a r y q c)) : Derives Γ (PacketReaderStepSyntax.state w r y q c) := by
  let R := advanceBody w B z o l v s a r y q c
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ (.conjR hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := HornBinderRules.under_body 2 hB R
  have hz2 : Derives Δ (.mem (old 2 z) (old 2 w)) := HornBinderRules.under_body 2 hz R
  have ho2 : Derives Δ (.mem (old 2 o) (old 2 w)) := HornBinderRules.under_body 2 ho R
  have hi2 := of_eq (PacketReaderStepSyntax.state_rename w l v s a (old 2)) (HornBinderRules.under_body 2 (.conjL hc) R)
  have hr := PacketReaderInputFields.rest_state _ _ _ _ _ _ _ hi2 (.conjL hR)
  exact of_eq (PacketReaderStepSyntax.state_rename w r y q c (old 2)).symm
    (PacketReaderStep.domain hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 hz2 ho2 hr (.conjR hR))

theorem unique_at_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c t j k d b x : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (headRest w l b x))
    (hc : Derives Γ (advance w B z o l v s a r y q c)) (hd : Derives Γ (advance w B z o l v s a t j k d)) :
    Derives Γ (PacketReaderStep.same r y q c t j k d) := by
  have hC := Derives.impE (.conjL (PacketReaderInputNormalize.at_cons hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hh)) hc
  have hD := Derives.impE (.conjL (PacketReaderInputNormalize.at_cons hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hh)) hd
  have hi := PacketReaderInputFields.rest_state _ _ _ _ _ _ _ (.conjL hC) hh
  exact PacketReaderStep.unique hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB (.conjL hh) hi (.conjR hC) (.conjR hD)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c t j k d : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hc : Derives Γ (advance w B z o l v s a r y q c)) (hd : Derives Γ (advance w B z o l v s a t j k d)) :
    Derives Γ (PacketReaderStep.same r y q c t j k d) := by
  let R := advanceBody w B z o l v s a r y q c
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ (.conjR hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := HornBinderRules.under_body 2 hB R
  have hc2 := of_eq (advance_rename w B z o l v s a r y q c (old 2)) (HornBinderRules.under_body 2 hc R)
  have hd2 := of_eq (advance_rename w B z o l v s a t j k d (old 2)) (HornBinderRules.under_body 2 hd R)
  exact of_eq (PacketReaderStep.same_rename r y q c t j k d (old 2)).symm
    (unique_at_cons hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 (.conjL hR) hc2 hd2)

theorem blocked_incompatible {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hr : Derives Γ (blocked w B z o l s)) (hc : Derives Γ (advance w B z o l v s a r y q c)) : Derives Γ .bot := by
  let R := blockedBody w B z o l s
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := HornBinderRules.under_body 2 hB R
  have hc2 := of_eq (advance_rename w B z o l v s a r y q c (old 2)) (HornBinderRules.under_body 2 hc R)
  have hs := Derives.impE (.conjL (PacketReaderInputNormalize.at_cons hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 (.conjL hR))) hc2
  exact .impE (PacketReaderGuards.reject_no_step hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 (.conjR hR)) (.conjR hs)

theorem invalid_state_no_advance {m} {Γ : Context m} (w B z o l v s a r y q c : Fin m)
    (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a).neg) : Derives Γ (advance w B z o l v s a r y q c).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjL (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketReaderInputStep
