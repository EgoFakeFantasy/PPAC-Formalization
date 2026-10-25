import PPAC.Migration.Internal.PacketReaderInputTransport

/-! Complete input witness blocks normalize to every actual Cons, and are impossible on Nil. -/
namespace PPAC.Migration.Internal.PacketReaderInputNormalize
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c b x : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (headRest w l b x)) :
    Derives Γ ((advance w B z o l v s a r y q c).iff
      ((PacketReaderStepSyntax.state w l v s a).conj (PacketReaderStepSyntax.step w B z o b x v s a r y q c))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := advance w B z o l v s a r y q c
    let R := advanceBody w B z o l v s a r y q c
    let Δ := Context.add R (raisedContext 2 (Context.add H Γ))
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    apply HornBinderRules.eliminate_many 2 R _ (.conjR hH)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) R
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) R)
    have hh2 := of_eq (headRest_rename w l b x (old 2)) (HornBinderRules.under_body 2 (add hh H) R)
    have hi2 := of_eq (PacketReaderStepSyntax.state_rename w l v s a (old 2)) (HornBinderRules.under_body 2 (.conjL hH) R)
    have he := PacketReaderInputFields.unique hZ2 _ _ _ _ _ _ hw2 (.conjL hR) hh2
    have hs := PacketReaderInputTransport.step_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjR hR)
    have ht := PacketReaderInputTransport.step_rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjR he) hs
    exact of_eq (by simp only [Formula.rename,PacketReaderStepSyntax.state_rename,PacketReaderStepSyntax.step_rename]) (.conjI hi2 ht)
  · apply Derives.impI
    have hH : Derives (Context.add ((PacketReaderStepSyntax.state w l v s a).conj (PacketReaderStepSyntax.step w B z o b x v s a r y q c)) Γ)
      ((PacketReaderStepSyntax.state w l v s a).conj (PacketReaderStepSyntax.step w B z o b x v s a r y q c)) := .hyp (Or.inl rfl)
    exact intro_advance _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL hH) (add hh _) (.conjR hH)

theorem blocked_at_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l s b x : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (headRest w l b x)) :
    Derives Γ ((blocked w B z o l s).iff (PacketReaderStepSyntax.reject B z o b s)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := blocked w B z o l s
    let R := blockedBody w B z o l s
    let Δ := Context.add R (raisedContext 2 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 2 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) R
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) R)
    have hh2 := of_eq (headRest_rename w l b x (old 2)) (HornBinderRules.under_body 2 (add hh H) R)
    have he := PacketReaderInputFields.unique hZ2 _ _ _ _ _ _ hw2 (.conjL hR) hh2
    exact of_eq (PacketReaderStepSyntax.reject_rename B z o b s (old 2)).symm
      (PacketReaderInputTransport.reject_head _ _ _ _ _ _ (.conjL he) (.conjR hR))
  · apply Derives.impI
    exact intro_blocked _ _ _ _ _ _ _ _ (add hh _) (.hyp (Or.inl rfl))

theorem nil_no_advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w l)) : Derives Γ (advance w B z o l v s a r y q c).neg := by
  apply Derives.impI
  let H := advance w B z o l v s a r y q c
  let R := advanceBody w B z o l v s a r y q c
  let Δ := Context.add R (raisedContext 2 (Context.add H Γ))
  have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
  apply HornBinderRules.eliminate_many 2 R _ (.conjR hH)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) R)
  have hn2 := of_eq (StructuralListSyntax.nilCode_rename w l (old 2)) (HornBinderRules.under_body 2 (add hn H) R)
  exact .impE (PacketReaderInputFields.not_nil hZ2 _ _ _ _ hw2 (.conjL hR)) hn2

theorem nil_no_blocked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l s : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w l)) : Derives Γ (blocked w B z o l s).neg := by
  apply Derives.impI
  let H := blocked w B z o l s
  let R := blockedBody w B z o l s
  let Δ := Context.add R (raisedContext 2 (Context.add H Γ))
  apply HornBinderRules.eliminate_many 2 R _ (.hyp (Or.inl rfl))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) R)
  have hn2 := of_eq (StructuralListSyntax.nilCode_rename w l (old 2)) (HornBinderRules.under_body 2 (add hn H) R)
  exact .impE (PacketReaderInputFields.not_nil hZ2 _ _ _ _ hw2 (.conjL hR)) hn2

end PPAC.Migration.Internal.PacketReaderInputNormalize
