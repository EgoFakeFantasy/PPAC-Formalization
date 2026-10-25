import PPAC.Migration.Internal.StructuralReverseIndexCons

/-! Actual reverse of Cons has every old reverse-tail field followed by the actual original head. -/
namespace PPAC.Migration.Internal.StructuralListReverseCons
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListReverseSyntax StructuralReverseIndexSyntax
open StructuralListFieldSyntax (field field_rename)
open StructuralListSyntax (consCode consCode_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_partner {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r i j J y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hm : Derives Γ (mirror w l i j)) (hL : Derives Γ (successor L l)) (hJ : Derives Γ (successor J j))
    (hc : Derives Γ (consCode w h t n)) (hu : Derives Γ (reading w t l u)) (hr : Derives Γ (reading w n L r)) :
    Derives Γ ((field w r i y).iff (field w u i y)) := by
  have hBig := StructuralReverseIndexCons.grow hZ w l L i j J hw hm hL hJ
  have hR := StructuralListReverseLaws.field_at_mirror hZ w n L r i J y hw hr hBig
  have hC := StructuralListFieldCons.successor_iff hZ w h t n j J y hw hh ht (.conjL (.conjR hm)) hJ hc
  have hU := StructuralListReverseLaws.field_at_mirror hZ w t l u i j y hw hu hm
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjR hU) _) (.impE (add (.conjL hC) _) (.impE (add (.conjL hR) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR hR) _) (.impE (add (.conjR hC) _) (.impE (add (.conjL hU) _) (.hyp (Or.inl rfl))))

theorem from_mirror {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r i j y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hm : Derives Γ (mirror w l i j)) (hL : Derives Γ (successor L l))
    (hc : Derives Γ (consCode w h t n)) (hu : Derives Γ (reading w t l u)) (hr : Derives Γ (reading w n L r)) :
    Derives Γ ((field w r i y).iff (field w u i y)) := by
  have hex := Derives.impE (OmegaSyntax.step_at w j (.conjL hw)) (.conjL (.conjR hm))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) j.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have ht1 : Derives Δ (.mem t.castSucc w.castSucc) := under ht R
  have hm1 := of_eq (mirror_rename w l i j Fin.castSucc) (under hm R)
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL R)
  have hc1 := of_eq (consCode_rename w h t n Fin.castSucc) (under hc R)
  have hu1 := of_eq (reading_rename w t l u Fin.castSucc) (under hu R)
  have hr1 := of_eq (reading_rename w n L r Fin.castSucc) (under hr R)
  simpa only [Formula.raise,Formula.rename,Formula.iff,field_rename] using at_partner hZ1 w.castSucc h.castSucc t.castSucc n.castSucc l.castSucc L.castSucc u.castSucc r.castSucc i.castSucc j.castSucc (Fin.last m) y.castSucc hw1 hh1 ht1 hm1 hL1 (.conjR hR) hc1 hu1 hr1

theorem prefix_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L u r i y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hl : Derives Γ (.mem l w))
    (hL : Derives Γ (successor L l)) (hc : Derives Γ (consCode w h t n))
    (hu : Derives Γ (reading w t l u)) (hr : Derives Γ (reading w n L r)) (hi : Derives Γ (.mem i l)) :
    Derives Γ ((field w r i y).iff (field w u i y)) := by
  let R := mirror w.castSucc l.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralReverseIndexExistence.exists_partner hZ w l i hw hl hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have ht1 : Derives Δ (.mem t.castSucc w.castSucc) := under ht R
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL R)
  have hc1 := of_eq (consCode_rename w h t n Fin.castSucc) (under hc R)
  have hu1 := of_eq (reading_rename w t l u Fin.castSucc) (under hu R)
  have hr1 := of_eq (reading_rename w n L r Fin.castSucc) (under hr R)
  simpa only [Formula.raise,Formula.rename,Formula.iff,field_rename] using from_mirror hZ1 w.castSucc h.castSucc t.castSucc n.castSucc l.castSucc L.castSucc u.castSucc r.castSucc i.castSucc (Fin.last m) y.castSucc hw1 hh1 ht1 hR hL1 hc1 hu1 hr1

theorem last_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L r z y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hl : Derives Γ (.mem l w))
    (hL : Derives Γ (successor L l)) (hc : Derives Γ (consCode w h t n))
    (hr : Derives Γ (reading w n L r)) (hz : Derives Γ (empty z)) : Derives Γ ((field w r l y).iff (.equal y h)) := by
  have hm := StructuralReverseIndexCons.last_zero hZ w l L z hw hl hL hz
  have hR := StructuralListReverseLaws.field_at_mirror hZ w n L r l z y hw hr hm
  have hC := StructuralListFieldCons.zero_iff hZ w h t n z y hw hh ht hc hz
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hC) _) (.impE (add (.conjL hR) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hR) _) (.impE (add (.conjR hC) _) (.hyp (Or.inl rfl)))

theorem last_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l L r y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hl : Derives Γ (.mem l w))
    (hL : Derives Γ (successor L l)) (hc : Derives Γ (consCode w h t n))
    (hr : Derives Γ (reading w n L r)) : Derives Γ ((field w r l y).iff (.equal y h)) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjL (.conjL hw))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have ht1 : Derives Δ (.mem t.castSucc w.castSucc) := under ht R
  have hl1 : Derives Δ (.mem l.castSucc w.castSucc) := under hl R
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL R)
  have hc1 := of_eq (consCode_rename w h t n Fin.castSucc) (under hc R)
  have hr1 := of_eq (reading_rename w n L r Fin.castSucc) (under hr R)
  simpa only [Formula.raise,Formula.rename,Formula.iff,field_rename] using last_at_zero hZ1 w.castSucc h.castSucc t.castSucc n.castSucc l.castSucc L.castSucc r.castSucc (Fin.last m) y.castSucc hw1 hh1 ht1 hl1 hL1 hc1 hr1 (.conjR hR)

end PPAC.Migration.Internal.StructuralListReverseCons
