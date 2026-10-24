import PPAC.Migration.Internal.PacketBytesExecutionFiberSyntax

/-! All joint IH and radix witnesses are discharged: actual byte execution is total and unique on exactly the independent input domain. -/
namespace PPAC.Migration.Internal.PacketBytesExecution
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketByteInputSyntax PacketBytesExecutionSyntax PacketBytesExecutionFiberSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_to_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (byteList w n)) (ht : Derives Γ (.mem t w)) : Derives Γ (fiber w n t) := by
  let U := (Formula.mem (Fin.last m) w.castSucc).conj (bytes w.castSucc n.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) (PacketBytesExecutionInduction.exists_output hZ w n t hw hn ht)
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have huniq : Derives Δ (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let H := bytes w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))
    have hZ2 := ZFContext.under hZ1 H
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
    have hA := of_eq (bytes_rename w.castSucc n.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hU) H)
    exact PacketBytesExecutionInduction.output_unique hZ2 w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 (.hyp (Or.inl rfl)) hA
  simpa only [Formula.raise,fiber_rename] using intro_fiber w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjL hU) (.conjR hU) huniq

theorem fiber_to_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (fiber w n t)) : Derives Γ ((byteList w n).conj (.mem t w)) := by
  let R := fiberBody w n t
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hB := Derives.conjR (Derives.conjL hR)
  have hn := PacketBytesExecutionInduction.input_domain hZ1 w.castSucc n.castSucc t.castSucc (Fin.last m) hw1 hB
  have ht := Derives.conjL (Derives.conjR (PacketBytesLaws.domain w.castSucc n.castSucc t.castSucc (Fin.last m) hB))
  have hout := Derives.conjI hn ht
  simpa only [Formula.raise,Formula.rename,byteList_rename] using hout

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((fiber w n t).iff ((byteList w n).conj (.mem t w))) :=
  .conjI (.impI (fiber_to_input (ZFContext.add hZ _) w n t (add hw _) (.hyp (Or.inl rfl))))
    (.impI (input_to_fiber (ZFContext.add hZ _) w n t (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))))

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((existsOutput w n t).iff ((byteList w n).conj (.mem t w))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsOutput w n t
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (bytes w.castSucc n.castSucc t.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    have hex : Derives (Context.add H Γ) (.ex R) := .hyp (Or.inl rfl)
    apply Derives.exE (p := R) hex
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hn := PacketBytesExecutionInduction.input_domain hZ1 w.castSucc n.castSucc t.castSucc (Fin.last m) hw1 (.conjR hR)
    have ht := Derives.conjL (Derives.conjR (PacketBytesLaws.domain w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjR hR)))
    have hout := Derives.conjI hn ht
    simpa only [Formula.raise,Formula.rename,byteList_rename] using hout
  · apply Derives.impI
    exact PacketBytesExecutionInduction.exists_output (ZFContext.add hZ _) w n t (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  exact fiber_iff (HornBinderRules.zf_many 2 hZ) (old 2 w) (slot 2 0) (slot 2 1) hw2

theorem reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (byteList w n).neg) : Derives Γ (bytes w n t a).neg := by
  apply Derives.impI
  exact .impE (add hn _) (PacketBytesExecutionInduction.input_domain (ZFContext.add hZ _) w n t a (add hw _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketBytesExecution
