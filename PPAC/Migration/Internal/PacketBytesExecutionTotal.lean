import PPAC.Migration.Internal.PacketBytesExecutionDescent

/-! Existence composes the actual smaller byte execution with a real total 256 cell, preserving the independent input guard. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionTotal
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketByteInputSyntax PacketBytesExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t h x : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hh : Derives Γ (byte h)) (hx : Derives Γ (byteList w x)) :
    Derives Γ (existsOutput w n t) := by
  have hp := PacketBytesExecutionDescent.input_tail_property hZ w n h x hw hi hc hh hx
  have hex := total_at w x t hp hx ht
  let U := (Formula.mem (Fin.last m) w.castSucc).conj (bytes w.castSucc x.castSucc t.castSucc (Fin.last m))
  let ΓU := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hex
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hh1 := of_eq (byte_rename h Fin.castSucc) (under hh U)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x n Fin.castSucc) (under hc U)
  have hU : Derives ΓU U := .hyp (Or.inl rfl)
  have hcell := PacketBytesExecutionAffine.exists_cell hZ1 w.castSucc h.castSucc (Fin.last m) hw1 hh1 (.conjL hU)
  let A := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (PacketAffineAcceptedSyntax.accepted true w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add A (Context.image Formula.raise ΓU)
  apply Derives.exE (p := A) hcell
  have hZ2 := ZFContext.under hZ1 A
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 A)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc x.castSucc n.castSucc Fin.castSucc) (under hc1 A)
  have hb2 := of_eq (bytes_rename w.castSucc x.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hU) A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hb := PacketBytesLaws.cons_bytes hZ2 w.castSucc.castSucc x.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc
    h.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hc2 (.conjR hA)
  simpa only [Formula.raise,existsOutput_rename] using intro_output w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) (.conjL hA) hb

theorem cons_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (PacketByteInputRecursionSyntax.actualCons w n)) : Derives Γ (existsOutput w n t) := by
  let R := PacketByteInputRecursionSyntax.actualBody w n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hc
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hi2 := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_body 2 hi R)
  have ht2 : Derives Δ (.mem (old 2 t) (old 2 w)) := HornBinderRules.under_body 2 ht R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (existsOutput_rename w n t (old 2)).symm
    (cons_point hZ2 (old 2 w) (old 2 n) (old 2 t) (slot 2 0) (slot 2 1) hw2 hi2 ht2 (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR)))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hn : Derives Γ (byteList w n)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsOutput w n t) := by
  have hc := Derives.impE (.conjL (PacketByteInputLaws.actual_iff hZ w n hw)) hn
  apply Derives.disjE hc
  · exact intro_output w n t t (add ht _) (PacketBytesLaws.nil_fold (ZFContext.add hZ _) w n t (add hw _) (.hyp (Or.inl rfl)) (add ht _))
  · exact cons_case (ZFContext.add hZ _) w n t (add hw _) (add hi _) (add ht _) (.hyp (Or.inl rfl))

theorem total_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (total w n) := by
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let H := byteList w n
  let T := Formula.mem (Fin.last m) w.castSucc
  let Δ := Context.add T (Context.image Formula.raise (Context.add H Γ))
  have hZ1 := ZFContext.under (ZFContext.add hZ H) T
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) T)
  have hi1 := of_eq (earlier_rename w n Fin.castSucc) (under (add hi H) T)
  have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
  have hn1 := of_eq (byteList_rename w n Fin.castSucc) (under hH T)
  have ht : Derives Δ T := .hyp (Or.inl rfl)
  exact point hZ1 w.castSucc n.castSucc (Fin.last m) hw1 hi1 hn1 ht

end PPAC.Migration.Internal.PacketBytesExecutionTotal
