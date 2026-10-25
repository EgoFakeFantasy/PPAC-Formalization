import PPAC.Migration.Internal.PacketReaderLengthArithmetic

/-! Actual seed length and adjacent remaining lengths discharge the conservation base and successor. -/
namespace PPAC.Migration.Internal.PacketReaderLengthPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderLengthSyntax PacketReaderConsumptionSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open StructuralListLengthSyntax (hasLength hasLength_rename)
open NaturalAdditionSyntax (sum sum_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N i a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N))
    (hi : Derives Γ (empty i)) (ha : Derives Γ (lengthAt w f i a)) : Derives Γ (sum w i a N) := by
  have he := OmegaUniversal.empty_unique z i (ZFContext.arithmetic hZ).base.extensionality (zero_at _ _ _ _ _ _ _ _ _ hh) hi
  have hs := StructuralListTraceOrder.edge_input_subst f z i n he (seed_at _ _ _ _ _ _ _ _ _ hh)
  have hInit := intro_length w f i N L (intro_at w f i L n hs hL) hN
  have hEq := PacketReaderLengthAt.unique hZ w f d i a N hw (sequence_at _ _ _ _ _ _ _ _ _ hh) ha hInit
  exact PacketReaderLengthArithmetic.zero_sum hZ w i a N hw hi (PacketReaderLengthAt.natural _ _ _ _ ha) hEq

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) (hi : Derives Γ (empty i)) :
    Derives Γ (balance w f N i) := by
  apply Derives.allI
  apply Derives.impI
  let H := lengthAt w.castSucc f.castSucc i.castSucc (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh H)
  have hL1 := of_eq (input_rename w n L Fin.castSucc) (under hL H)
  have hN1 := of_eq (hasLength_rename w L N Fin.castSucc) (under hN H)
  have hi1 := of_eq (empty_rename i Fin.castSucc) (under hi H)
  exact zero_value hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 hL1 hN1 hi1 (.hyp (Or.inl rfl))

theorem adjacent_lengths {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i j a b : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hi : Derives Γ (.mem i l)) (hj : Derives Γ (successor j i))
    (ha : Derives Γ (lengthAt w f i a)) (hb : Derives Γ (lengthAt w f j b)) : Derives Γ (successor a b) := by
  let R := (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).conj (hasLength w.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ha
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb1 := of_eq (lengthAt_rename w f j b Fin.castSucc) (under hb R)
  let T := (inputAt w.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1))).conj
    (hasLength w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hb1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hh2 : Derives Ξ (history w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc r.castSucc.castSucc l.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,history_rename]) (under (under hh R) T)
  have hi2 : Derives Ξ (.mem i.castSucc.castSucc l.castSucc.castSucc) := under (under hi R) T
  have hj2 : Derives Ξ (successor j.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise,successor_rename]) (under (under hj R) T)
  have hI := of_eq (inputAt_rename w.castSucc f.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) T)
  have hA := of_eq (hasLength_rename w.castSucc (Fin.last m) a.castSucc Fin.castSucc) (under (.conjR hR) T)
  have ht := PacketReaderHistoryConsumption.adjacent hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hh2 hi2 hj2 hI (.conjL hT)
  have hout := PacketReaderTailLength.successor_length hZ2 _ _ _ _ _ hw2 ht hA (.conjR hT)
  simpa only [Formula.raise,successor_rename] using hout

theorem successor_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f N i j b : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hBal : Derives Γ (balance w f N i)) (hj : Derives Γ (successor j i))
    (hb : Derives Γ (lengthAt w f j b)) : Derives Γ (sum w j b N) := by
  have hSeq := sequence_at _ _ _ _ _ _ _ _ _ hh
  have hjD := PacketReaderLengthAt.domain hZ w f d j b hSeq hb
  have hiL := SyntaxIndexLiftOrder.predecessor_member hZ w l d j i hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh) hjD hj
  have hiD := InsertLogic.old_member d l l i (successor_at _ _ _ _ _ _ _ _ _ hh) hiL
  have hiN := StructuralListTraceOrder.member_member hZ w i l hw (length_at _ _ _ _ _ _ _ _ _ hh) hiL
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (lengthAt w.castSucc f.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderLengthAt.exists_at hZ w B z o n r l d f i hw hh hiD)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh R)
  have hi1 : Derives Δ (.mem i.castSucc l.castSucc) := under hiL R
  have hiN1 : Derives Δ (.mem i.castSucc w.castSucc) := under hiN R
  have hj1 := of_eq (successor_rename j i Fin.castSucc) (under hj R)
  have hb1 := of_eq (lengthAt_rename w f j b Fin.castSucc) (under hb R)
  have hBal1 := of_eq (balance_rename w f N i Fin.castSucc) (under hBal R)
  have hs := adjacent_lengths hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 hi1 hj1 (.conjR hR) hb1
  have hSum := balance_at _ _ _ _ _ hBal1 (.conjR hR)
  have hout := PacketReaderLengthArithmetic.transfer hZ1 _ _ _ _ _ _ hw1 hiN1 (PacketReaderLengthAt.natural _ _ _ _ hb1) hj1 hs hSum
  simpa only [Formula.raise,sum_rename] using hout

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f N i j : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hBal : Derives Γ (balance w f N i)) (hj : Derives Γ (successor j i)) : Derives Γ (balance w f N j) := by
  apply Derives.allI
  apply Derives.impI
  let H := lengthAt w.castSucc f.castSucc j.castSucc (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh H)
  have hBal1 := of_eq (balance_rename w f N i Fin.castSucc) (under hBal H)
  have hj1 := of_eq (successor_rename j i Fin.castSucc) (under hj H)
  exact successor_value hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 hBal1 hj1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderLengthPoint
