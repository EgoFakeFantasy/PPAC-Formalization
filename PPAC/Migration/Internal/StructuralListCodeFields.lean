import PPAC.Migration.Internal.StructuralListCodeLength

/-! 相同完整字段的实际Cons头相等、尾字段相同；覆盖任意内部索引及输出。 -/
namespace PPAC.Migration.Internal.StructuralListCodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListLengthSyntax StructuralListFieldSyntax StructuralListCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem head_subst {m} {Γ : Context m} (w h k t n : Fin m) (he : Derives Γ (.equal h k))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (consCode w k t n) := by
  have hi : Derives Γ ((consCode w.castSucc (Fin.last m) t.castSucc n.castSucc).instantiate h) := by
    simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (consCode w.castSucc (Fin.last m) t.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem tail_subst {m} {Γ : Context m} (w h t u n : Fin m) (he : Derives Γ (.equal t u))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (consCode w h u n) := by
  have hi : Derives Γ ((consCode w.castSucc h.castSucc (Fin.last m) n.castSucc).instantiate t) := by
    simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (consCode w.castSucc h.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem heads_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t a k u b : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hk : Derives Γ (.mem k w)) (hu : Derives Γ (.mem u w))
    (ha : Derives Γ (consCode w h t a)) (hb : Derives Γ (consCode w k u b)) (he : Derives Γ (agree w s a b)) : Derives Γ (.equal h k) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hzEx : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hzEx
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs Z
  have ha1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc a.castSucc) := by simpa only [Formula.raise, consCode_rename] using under ha Z
  have hb1 : Derives Δ (consCode w.castSucc k.castSucc u.castSucc b.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hb Z
  have he1 : Derives Δ (agree w.castSucc s.castSucc a.castSucc b.castSucc) := by simpa only [Formula.raise, agree_rename] using under he Z
  have hZZ : Derives Δ Z := .hyp (Or.inl rfl)
  have hzR := GodelUnpairArithmetic.zero_below hZ1 _ _ _ hw1 (.conjR hZZ) (under hr Z)
  have hzS := NaturalAdditionBounds.into_successor _ _ _ hzR hs1
  have hfA := StructuralListFieldCons.zero_value hZ1 _ _ _ _ _ hw1 (under hh Z) (under ht Z) ha1 (.conjR hZZ)
  have hfB := Derives.impE (.conjL (agree_at _ _ _ _ _ h.castSucc he1 hzS)) hfA
  exact StructuralListFieldCons.zero_point hZ1 _ _ _ _ _ _ hw1 (under hk Z) (under hu Z) hb1 (.conjR hZZ) hfB

theorem tail_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t a k u b i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hk : Derives Γ (.mem k w)) (hu : Derives Γ (.mem u w))
    (ha : Derives Γ (consCode w h t a)) (hb : Derives Γ (consCode w k u b)) (he : Derives Γ (agree w s a b))
    (hi : Derives Γ (.mem i r)) : Derives Γ ((field w t i y).iff (field w u i y)) := by
  have hiW := StructuralListTraceOrder.member_member hZ w i r hw hr hi
  let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) i.castSucc)
  let Δ := Context.add J (Context.image Formula.raise Γ)
  have hjEx : Derives Γ (.ex J) := .impE (OmegaSyntax.step_at w i (.conjL hw)) hiW
  apply Derives.exE (p := J) hjEx
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ J
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw J
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs J
  have ha1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc a.castSucc) := by simpa only [Formula.raise, consCode_rename] using under ha J
  have hb1 : Derives Δ (consCode w.castSucc k.castSucc u.castSucc b.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hb J
  have he1 : Derives Δ (agree w.castSucc s.castSucc a.castSucc b.castSucc) := by simpa only [Formula.raise, agree_rename] using under he J
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hjR := GodelPairArithmetic.successor_below hZ1 _ _ _ _ hw1 (under hiW J) (under hr J) (.conjR hJ) (under hi J)
  have hjS := NaturalAdditionBounds.into_successor _ _ _ hjR hs1
  have hA := StructuralListFieldCons.successor_iff hZ1 _ _ _ _ _ _ y.castSucc hw1 (under hh J) (under ht J) (under hiW J) (.conjR hJ) ha1
  have hB := StructuralListFieldCons.successor_iff hZ1 _ _ _ _ _ _ y.castSucc hw1 (under hk J) (under hu J) (under hiW J) (.conjR hJ) hb1
  have hAB := agree_at _ _ _ _ _ y.castSucc he1 hjS
  have hout := StructuralListSuffixArithmetic.iff_trans (.conjI (.conjR hA) (.conjL hA)) (StructuralListSuffixArithmetic.iff_trans hAB hB)
  simpa only [Formula.raise, Formula.rename, Formula.iff, field_rename] using hout

theorem agree_tails {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t a k u b : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hk : Derives Γ (.mem k w)) (hu : Derives Γ (.mem u w))
    (ha : Derives Γ (consCode w h t a)) (hb : Derives Γ (consCode w k u b)) (he : Derives Γ (agree w s a b)) : Derives Γ (agree w r t u) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc r.castSucc.castSucc
  let Δ := Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) M
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have ha2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift ha
  have hb2 : Derives Δ (consCode w.castSucc.castSucc k.castSucc.castSucc u.castSucc.castSucc b.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hb
  have he2 : Derives Δ (agree w.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := by simpa only [Formula.raise, agree_rename] using lift he
  exact tail_point hZ2 _ _ _ _ _ _ _ _ _ _ _ hw2 (lift hr) hs2 (lift hh) (lift ht) (lift hk) (lift hu) ha2 hb2 he2 (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListCodeFields
