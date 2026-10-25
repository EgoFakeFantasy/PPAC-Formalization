import PPAC.Migration.Internal.PacketReaderInputProjection

/-! Actual source/target input fields in every coded transition consume one real Cons cell, including arbitrary internal candidate codes. -/
namespace PPAC.Migration.Internal.PacketReaderCodedConsumption
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l v s a x y q c : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (PacketReaderStateSyntax.code w l v s a n))
    (hr : Derives Γ (PacketReaderStateSyntax.code w x y q c r)) (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) :
    Derives Γ (tail w l x) := by
  have hex := Derives.impE (.conjL (PacketReaderCodedNormalize.at_source hZ w B z o n r l v s a hw hn)) ht
  let R := PacketReaderCodedSyntax.nextBody w B z o l v s a r
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hr4 := of_eq (PacketReaderStateSyntax.code_rename w x y q c r (old 4)) (HornBinderRules.under_body 4 hr R)
  have he := Derives.conjL (PacketReaderStateCode.fields_unique hZ4 _ _ _ _ _ _ _ _ _ _ hw4 (.conjL hR) hr4)
  have hl := PacketReaderRawConsumption.raw_tail _ _ _ _ _ _ _ _ _ _ _ _ (.conjR hR)
  exact of_eq (tail_rename w l x (old 4)).symm (PacketReaderConsumptionTransport.tail_target _ _ _ _ he hl)

theorem at_inputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l x : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (input w n l)) (hr : Derives Γ (input w r x))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (tail w l x) := by
  let R := inputBody w n l
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hn
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hr3 := of_eq (input_rename w r x (old 3)) (HornBinderRules.under_body 3 hr R)
  have ht3 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r (old 3)) (HornBinderRules.under_body 3 ht R)
  let T := inputBody (old 3 w) (old 3 r) (old 3 x)
  let Ξ := Context.add T (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 T _ hr3
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ6 := HornBinderRules.zf_body 3 hZ3 T
  have hw6 := of_eq (omega_rename (old 3 w) (old 3)) (HornBinderRules.under_body 3 hw3 T)
  have hn6 := of_eq (PacketReaderStateSyntax.code_rename (old 3 w) (old 3 l) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) (old 3)) (HornBinderRules.under_body 3 hR T)
  have ht6 := of_eq (PacketReaderCodedSyntax.step_rename (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (old 3 r) (old 3)) (HornBinderRules.under_body 3 ht3 T)
  exact of_eq (by simp only [tail_rename]) (at_codes hZ6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw6 hn6 hT ht6)

theorem strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l x : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (input w n l)) (hr : Derives Γ (input w r x))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (.mem x l) :=
  PacketReaderRawConsumption.tail_strict hZ w l x hw (at_inputs hZ w B z o n r l x hw hn hr ht)

end PPAC.Migration.Internal.PacketReaderCodedConsumption
