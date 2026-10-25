import PPAC.Migration.Internal.PacketReaderStoppingInduction

/-! Initial input length excludes the overlong prefix branch; a genuine stopped graph exists for every actual source carrier. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open PacketReaderConsumptionSyntax (input input_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem exclude_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L N j : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N))
    (hj : Derives Γ (successor j N)) (hp : Derives Γ (prefixAt w B z o n j)) : Derives Γ .bot := by
  let R := prefixBody w B z o n j
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hL3 := of_eq (input_rename w n L (old 3)) (HornBinderRules.under_body 3 hL R)
  have hN3 := of_eq (hasLength_rename w L N (old 3)) (HornBinderRules.under_body 3 hN R)
  have hj3 := of_eq (successor_rename j N (old 3)) (HornBinderRules.under_body 3 hj R)
  have hNot := PacketReaderLengthBounds.no_too_long_history hZ3 (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (slot 3 0) (old 3 j) (slot 3 1) (slot 3 2) (old 3 L) (old 3 N) hw3 hR hL3 hN3
  exact .impE hNot (InsertLogic.new_member _ _ _ hj3)

theorem from_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) : Derives Γ (complete w B z o n) := by
  have hall := PacketReaderStoppingInduction.all_progress hZ w B z o n hw hz hc
  have hNN := StructuralListLengthBasic.length_member w L N hN
  have hex := Derives.impE (OmegaSyntax.step_at w N (.conjL hw)) hNN
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) N.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hL1 := of_eq (input_rename w n L Fin.castSucc) (under hL R)
  have hN1 := of_eq (hasLength_rename w L N Fin.castSucc) (under hN R)
  have hall1 := of_eq (allProgress_rename w B z o n Fin.castSucc) (under hall R)
  have hp := all_at _ _ _ _ _ _ hall1 (.conjL hR)
  simp only [Formula.raise,complete_rename]
  apply Derives.disjE hp
  · exact .hyp (Or.inl rfl)
  · let P := prefixAt w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)
    exact .botE (exclude_prefix (ZFContext.add hZ1 P) _ _ _ _ _ _ _ _ (add hw1 P) (add hL1 P) (add hN1 P) (add (.conjR hR) P) (.hyp (Or.inl rfl)))

theorem from_actual_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) : Derives Γ (complete w B z o n) := by
  have hCarrier := PacketReaderStateSyntax.intro_carrier w L v s a n hc
  have hInput := PacketReaderConsumptionSyntax.intro_input w n L v s a hc
  have hex := StructuralListLengthBasic.exists_length w L (.conjL (.conjL hc))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc L.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have hc1 := of_eq (PacketReaderStateSyntax.carrier_rename w n Fin.castSucc) (under hCarrier R)
  have hi1 := of_eq (input_rename w n L Fin.castSucc) (under hInput R)
  simpa only [Formula.raise,complete_rename] using from_length hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc L.castSucc (Fin.last m) hw1 hz1 hc1 hi1 (.conjR hR)

theorem exists_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (complete w B z o n) := by
  let R := PacketReaderStateSyntax.carrierBody w n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz R)
  exact of_eq (complete_rename w B z o n (old 4)).symm
    (from_actual_code hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hz4 hR)

end PPAC.Migration.Internal.PacketReaderStoppingExistence
