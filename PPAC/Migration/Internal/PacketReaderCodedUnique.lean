import PPAC.Migration.Internal.PacketReaderCodedNormalize

/-! Code injectivity and the full raw reader step prove coded determinism for every internal candidate code. -/
namespace PPAC.Migration.Internal.PacketReaderCodedUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStateSyntax PacketReaderCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (code w l v s a n))
    (hr : Derives Γ (step w B z o n r)) (ht : Derives Γ (step w B z o n t)) : Derives Γ (.equal r t) := by
  have hx := Derives.impE (.conjL (PacketReaderCodedNormalize.at_source hZ w B z o n r l v s a hw hc)) hr
  have hy := Derives.impE (.conjL (PacketReaderCodedNormalize.at_source hZ w B z o n t l v s a hw hc)) ht
  let R := nextBody w B z o l v s a r
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hx
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hy4 := of_eq (nextAt_rename w B z o l v s a t (old 4)) (HornBinderRules.under_body 4 hy R)
  let T := nextBody (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 v) (old 4 s) (old 4 a) (old 4 t)
  let Ξ := Context.add T (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 T _ hy4
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ8 := HornBinderRules.zf_body 4 hZ4 T
  have hw8 := of_eq (omega_rename (old 4 w) (old 4)) (HornBinderRules.under_body 4 hw4 T)
  have hB8 : Derives Ξ (.mem (old 4 (old 4 B)) (old 4 (old 4 w))) := HornBinderRules.under_body 4 hB4 T
  have hc8 := of_eq (code_rename (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 r) (old 4)) (HornBinderRules.under_body 4 (.conjL hR) T)
  have hx8 := of_eq (PacketReaderInputSyntax.advance_rename (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 v) (old 4 s) (old 4 a) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4))
    (HornBinderRules.under_body 4 (.conjR hR) T)
  have he := PacketReaderInputStep.unique hZ8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw8 hB8 hx8 (.conjR hT)
  have hc' := PacketReaderCodedTransport.align_code _ _ _ _ _ _ _ _ _ _ he hc8
  exact PacketReaderStateCode.unique hZ8 _ _ _ _ _ _ _ hw8 hc' (.conjL hT)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hr : Derives Γ (step w B z o n r))
    (ht : Derives Γ (step w B z o n t)) : Derives Γ (.equal r t) := by
  let R := stepBody w B z o n r
  let Δ := Context.add R (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ8 := HornBinderRules.zf_body 8 hZ R
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw R)
  have hB8 : Derives Δ (.mem (old 8 B) (old 8 w)) := HornBinderRules.under_body 8 hB R
  have hr8 := of_eq (step_rename w B z o n r (old 8)) (HornBinderRules.under_body 8 hr R)
  have ht8 := of_eq (step_rename w B z o n t (old 8)) (HornBinderRules.under_body 8 ht R)
  exact at_source hZ8 _ _ _ _ _ _ _ _ _ _ _ hw8 hB8 (.conjL hR) hr8 ht8

end PPAC.Migration.Internal.PacketReaderCodedUnique
