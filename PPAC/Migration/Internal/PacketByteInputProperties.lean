import PPAC.Migration.Internal.PacketByteInputBounds

/-! Validity, fixed actual lengths, Nil construction and full typed Cons transfer for the independent input guard. -/
namespace PPAC.Migration.Internal.PacketByteInputProperties
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListLengthSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem valid {m} {Γ : Context m} (w C n : Fin m) (hi : Derives Γ (inputAt w C n)) : Derives Γ (StructuralListTraceSyntax.valid w n) := by
  let R := inputBody w C n
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (StructuralListTraceSyntax.valid_rename w n (old 2)).symm (StructuralListEncodeReadback.encoding_valid _ _ _ _ (.conjL hR))

theorem natural {m} {Γ : Context m} (w C n : Fin m) (hi : Derives Γ (inputAt w C n)) : Derives Γ (.mem n w) :=
  StructuralListValidity.range _ _ (valid w C n hi)

theorem radix_subst {m} {Γ : Context m} (w C n D : Fin m) (he : Derives Γ (.equal C D)) (hi : Derives Γ (inputAt w C n)) : Derives Γ (inputAt w D n) := by
  let P := inputAt w.castSucc (Fin.last m) n.castSucc
  have h0 : P.instantiate C = inputAt w C n := by simp only [P,Formula.instantiate,inputAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate D = inputAt w D n := by simp only [P,Formula.instantiate,inputAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hi))

theorem bounds_length_subst {m} {Γ : Context m} (w C n l k : Fin m) (he : Derives Γ (.equal l k)) (hb : Derives Γ (bounds w C n l)) : Derives Γ (bounds w C n k) := by
  let P := bounds w.castSucc C.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate l = bounds w C n l := by simp only [P,Formula.instantiate,bounds_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate k = bounds w C n k := by simp only [P,Formula.instantiate,bounds_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hb))

theorem at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n l : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (inputAt w C n)) (hl : Derives Γ (hasLength w n l)) : Derives Γ (bounds w C n l) := by
  let R := lengthCase w.castSucc C.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketByteInputGraph.to_length w C n hi)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 := of_eq (hasLength_rename w n l Fin.castSucc) (under hl R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := StructuralListLengthUnique.unique (ZFContext.under hZ R) w.castSucc n.castSucc (Fin.last m) l.castSucc hw1 (.conjL hR) hl1
  simpa only [Formula.raise,bounds_rename] using bounds_length_subst _ _ _ _ _ he (.conjR hR)

theorem nil_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n)) : Derives Γ (inputAt w C n) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (StructuralListSyntax.nilCode w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.nilCode_rename] using OrderedPairElimination.under_two hn U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hl := StructuralListLengthConstruct.nil_length hZ2 (old 2 w) (old 2 n) (Fin.last m).castSucc hw2 hn2 (.conjL hU)
  have hb := PacketByteInputBounds.empty_bounds (old 2 w) (old 2 C) (old 2 n) (Fin.last m).castSucc (.conjL hU)
  simpa only [Formula.raise,inputAt_rename,HornBinderSyntax.old] using PacketByteInputGraph.from_length_at hZ2 (old 2 w) (old 2 C) (old 2 n) (Fin.last m).castSucc hw2 hl hb

theorem cons_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C h t n : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (.mem C w)) (hh : Derives Γ (.mem h C))
    (hi : Derives Γ (inputAt w C t)) (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) : Derives Γ (inputAt w C n) := by
  have hhW := StructuralListTraceOrder.member_member hZ w h C hw hC hh
  have htW := natural w C t hi
  let L := lengthCase w.castSucc C.castSucc t.castSucc (Fin.last m)
  let ΓL := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) (PacketByteInputGraph.to_length w C t hi)
  have hZ1 := ZFContext.under hZ L
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw L)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under hc L)
  have hL : Derives ΓL L := .hyp (Or.inl rfl)
  have hr := StructuralListLengthBasic.length_member _ _ _ (.conjL hL)
  let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add S (Context.image Formula.raise ΓL)
  apply Derives.exE (p := S) (Derives.impE (step_at _ _ (.conjL hw1)) hr)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc t.castSucc n.castSucc Fin.castSucc) (under hc1 S)
  have hL2 := of_eq (lengthCase_rename w.castSucc C.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under hL S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hlen := StructuralListLengthConstruct.cons_length hZ2 w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (under (under hhW L) S) hc2 (.conjL hL2) (.conjR hS)
  have hbound := PacketByteInputBounds.cons_bounds hZ2 w.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc hw2 (under hr S) (.conjR hS) (under (under hhW L) S) (under (under htW L) S) hc2 (.conjR hL2) (under (under hh L) S)
  simpa only [Formula.raise,inputAt_rename] using PacketByteInputGraph.from_length_at hZ2 w.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) hw2 hlen hbound

theorem typed_cons_inverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) (hi : Derives Γ (inputAt w C n)) :
    Derives Γ ((Formula.mem h C).conj (inputAt w C t)) := by
  let L := lengthCase w.castSucc C.castSucc n.castSucc (Fin.last m)
  let ΓL := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) (PacketByteInputGraph.to_length w C n hi)
  have hZ1 := ZFContext.under hZ L
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw L)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under hc L)
  have hL : Derives ΓL L := .hyp (Or.inl rfl)
  have hp := StructuralListLengthRules.cons_predecessor hZ1 w.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m)
    hw1 (under hh L) (under ht L) hc1 (.conjL hL)
  let R := ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))).conj
    (hasLength w.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add R (Context.image Formula.raise ΓL)
  apply Derives.exE (p := R) hp
  have hZ2 := ZFContext.under hZ1 R
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 R)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc t.castSucc n.castSucc Fin.castSucc) (under hc1 R)
  have hb2 := of_eq (bounds_rename w.castSucc C.castSucc n.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hL) R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hhead := PacketByteInputBounds.head_bound hZ2 w.castSucc.castSucc C.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL (.conjL hR)) (.conjR (.conjL hR)) (under (under hh L) R) (under (under ht L) R) hc2 hb2
  have htail := PacketByteInputBounds.tail_bounds hZ2 w.castSucc.castSucc C.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL (.conjL hR)) (.conjR (.conjL hR)) (under (under hh L) R) (under (under ht L) R) hc2 hb2
  have hin := PacketByteInputGraph.from_length_at hZ2 w.castSucc.castSucc C.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjR hR) htail
  have hout := Derives.conjI hhead hin
  simpa only [Formula.raise,Formula.rename,inputAt_rename] using hout

end PPAC.Migration.Internal.PacketByteInputProperties
