import PPAC.Migration.Internal.PacketByteInputGraph

/-! Original zero/successor field equations transfer every internal byte bound through real typed Cons. -/
namespace PPAC.Migration.Internal.PacketByteInputBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListSyntax StructuralListFieldSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem empty_bounds {m} {Γ : Context m} (w C n z : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (bounds w C n z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (Fin.last m).castSucc z.castSucc.castSucc
  let Y := field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_many 2 hz)
  exact .botE (.impE (add (add (empty_at (old 2 z) (Fin.last m).castSucc hz2) I) Y) (.hyp (Or.inr (Or.inl rfl))))

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C r s h t n i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hb : Derives Γ (bounds w C t r)) (hi : Derives Γ (.mem i s))
    (hByte : Derives Γ (.mem h C)) (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y C) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r (ZFContext.arithmetic hZ).base.extensionality hw hr hs
  have hiW := StructuralListTraceOrder.member_member hZ w i s hw hsW hi
  have hd := OmegaStructureAlgebra.decomposition_at w i
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiW
  apply Derives.disjE hd
  · have he := StructuralListFieldCons.zero_point (ZFContext.add hZ _) _ _ _ _ _ _
      (add hw _) (add hh _) (add ht _) (add hc _) (.hyp (Or.inl rfl)) (add hy _)
    exact mem_subst (eq_symm he) (add hByte _)
  · let P := OmegaStructureSyntax.predecessor w i
    let Γp := Context.add P Γ
    let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add J (Context.image Formula.raise Γp)
    have hj : Derives Γp (.ex J) := .hyp (Or.inl rfl)
    apply Derives.exE (p := J) hj
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) J
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp P) J
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
    have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
    have hb1 : Derives Δ (bounds w.castSucc C.castSucc t.castSucc r.castSucc) := by simpa only [Formula.raise, bounds_rename] using lift hb
    have hy1 : Derives Δ (field w.castSucc n.castSucc i.castSucc y.castSucc) := by simpa only [Formula.raise, field_rename] using lift hy
    have hJ : Derives Δ J := .hyp (Or.inl rfl)
    have hjR := StructuralListSuffixArithmetic.predecessor_inside hZ1 _ _ _ _ _ hw1 (lift hr) hs1 (.conjR hJ) (lift hi)
    have hyT := StructuralListFieldCons.successor_forward hZ1 _ _ _ _ _ _ _ hw1 (lift hh) (lift ht) (.conjL hJ) (.conjR hJ) hc1 hy1
    exact bounds_at _ _ _ _ _ _ hb1 hjR hyT

theorem cons_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C r s h t n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hb : Derives Γ (bounds w C t r)) (hByte : Derives Γ (.mem h C)) : Derives Γ (bounds w C n s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (Fin.last m).castSucc s.castSucc.castSucc
  let Y := field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.add I (raisedContext 2 Γ))
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) I) Y
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ (q.rename (old 2)) := add (add (HornBinderRules.under_many 2 hq) I) Y
  have hw2 := of_eq (omega_rename w (old 2)) (lift hw)
  have hs2 := of_eq (successor_rename s r (old 2)) (lift hs)
  have hc2 := of_eq (consCode_rename w h t n (old 2)) (lift hc)
  have hb2 := of_eq (bounds_rename w C t r (old 2)) (lift hb)
  exact cons_point hZ2 (old 2 w) (old 2 C) (old 2 r) (old 2 s) (old 2 h) (old 2 t) (old 2 n) (Fin.last m).castSucc (Fin.last (m+1))
    hw2 (lift hr) hs2 (lift hh) (lift ht) hc2 hb2 (.hyp (Or.inr (Or.inl rfl))) (lift hByte) (.hyp (Or.inl rfl))

theorem head_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C r s h t n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hb : Derives Γ (bounds w C n s)) : Derives Γ (.mem h C) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (raisedContext 2 Γ)
  apply StructuralListUnits.with_units w _ hw
  have hZ2 := HornBinderRules.zf_body 2 hZ U
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw U)
  have hs2 := of_eq (successor_rename s r (old 2)) (HornBinderRules.under_body 2 hs U)
  have hc2 := of_eq (consCode_rename w h t n (old 2)) (HornBinderRules.under_body 2 hc U)
  have hb2 := of_eq (bounds_rename w C n s (old 2)) (HornBinderRules.under_body 2 hb U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hz := GodelUnpairArithmetic.zero_below hZ2 (old 2 w) (Fin.last m).castSucc (old 2 r) hw2 (.conjL hU) (HornBinderRules.under_body 2 hr U)
  have hi := NaturalOrderBasic.below_successor _ _ _ hs2 hz
  have hf := StructuralListFieldCons.zero_value hZ2 (old 2 w) (old 2 h) (old 2 t) (old 2 n) (Fin.last m).castSucc
    hw2 (HornBinderRules.under_body 2 hh U) (HornBinderRules.under_body 2 ht U) hc2 (.conjL hU)
  exact bounds_at _ _ _ _ _ _ hb2 hi hf

theorem tail_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C r s h t n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hb : Derives Γ (bounds w C n s)) : Derives Γ (bounds w C t r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (Fin.last m).castSucc r.castSucc.castSucc
  let Y := field w.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let ΓY := Context.add Y (Context.add I (raisedContext 2 Γ))
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) I) Y
  have lift {q : Formula m} (hq : Derives Γ q) : Derives ΓY (q.rename (old 2)) := add (add (HornBinderRules.under_many 2 hq) I) Y
  have hw2 := of_eq (omega_rename w (old 2)) (lift hw)
  have hs2 := of_eq (successor_rename s r (old 2)) (lift hs)
  have hc2 := of_eq (consCode_rename w h t n (old 2)) (lift hc)
  have hb2 := of_eq (bounds_rename w C n s (old 2)) (lift hb)
  have hi : Derives ΓY I := .hyp (Or.inr (Or.inl rfl))
  have hy : Derives ΓY Y := .hyp (Or.inl rfl)
  have hiW := StructuralListTraceOrder.member_member hZ2 (old 2 w) (Fin.last m).castSucc (old 2 r) hw2 (lift hr) hi
  let J := (Formula.mem (Fin.last (m+2)) (old 2 w).castSucc).conj (successor (Fin.last (m+2)) (Fin.last m).castSucc.castSucc)
  let Δ := Context.add J (Context.image Formula.raise ΓY)
  apply Derives.exE (p := J) (Derives.impE (step_at _ _ (.conjL hw2)) hiW)
  have hZ3 := ZFContext.under hZ2 J
  have hw3 := of_eq (omega_rename (old 2 w) Fin.castSucc) (under hw2 J)
  have hs3 := of_eq (successor_rename (old 2 s) (old 2 r) Fin.castSucc) (under hs2 J)
  have hc3 := of_eq (consCode_rename (old 2 w) (old 2 h) (old 2 t) (old 2 n) Fin.castSucc) (under hc2 J)
  have hb3 := of_eq (bounds_rename (old 2 w) (old 2 C) (old 2 n) (old 2 s) Fin.castSucc) (under hb2 J)
  have hy3 := of_eq (field_rename (old 2 w) (old 2 t) (Fin.last m).castSucc (Fin.last (m+1)) Fin.castSucc) (under hy J)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hle := GodelPairArithmetic.successor_below hZ3 _ _ _ _ hw3 (under hiW J) (under (lift hr) J) (.conjR hJ) (under hi J)
  have hin := NaturalOrderBasic.below_successor _ _ _ hs3 hle
  have hfield := StructuralListFieldCons.successor_backward hZ3 _ _ _ _ _ _ _ hw3 (under (lift hh) J) (under (lift ht) J)
    (under hiW J) (.conjR hJ) hc3 hy3
  exact bounds_at _ _ _ _ _ _ hb3 hin hfield

end PPAC.Migration.Internal.PacketByteInputBounds
