import PPAC.Migration.Internal.PacketReaderRawConsumption

/-! Actual state-input projection has a valid-list range and is single-valued on every accepted state code. -/
namespace PPAC.Migration.Internal.PacketReaderInputProjection
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem valid_input {m} {Γ : Context m} (w n l : Fin m) (hi : Derives Γ (input w n l)) :
    Derives Γ (StructuralListTraceSyntax.valid w l) := by
  let R := inputBody w n l
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (StructuralListTraceSyntax.valid_rename w l (old 3)).symm (.conjL (.conjL hR))

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l v s a L : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketReaderStateSyntax.code w l v s a n))
    (hi : Derives Γ (input w n L)) : Derives Γ (.equal L l) := by
  let R := inputBody w n L
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hc3 := of_eq (PacketReaderStateSyntax.code_rename w l v s a n (old 3)) (HornBinderRules.under_body 3 hc R)
  exact .conjL (PacketReaderStateCode.fields_unique hZ3 _ _ _ _ _ _ _ _ _ _ hw3 hR hc3)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l L : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (input w n l)) (hL : Derives Γ (input w n L)) : Derives Γ (.equal l L) := by
  let R := inputBody w n l
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hl
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hL3 := of_eq (input_rename w n L (old 3)) (HornBinderRules.under_body 3 hL R)
  exact eq_symm (at_code hZ3 _ _ _ _ _ _ _ hw3 hR hL3)

theorem exists_of_carrier {m} {Γ : Context m} (w n : Fin m) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (existsInput w n) := by
  let R := PacketReaderStateSyntax.carrierBody w n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hi := intro_input _ _ _ _ _ _ hR
  have hout : Derives Δ (existsInput (old 4 w) (old 4 n)) := by
    apply Derives.exI (slot 4 0)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListTraceSyntax.valid_rename,input_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (.conjI (.conjL (.conjL hR)) hi)
  exact of_eq (existsInput_rename w n (old 4)).symm hout

end PPAC.Migration.Internal.PacketReaderInputProjection
