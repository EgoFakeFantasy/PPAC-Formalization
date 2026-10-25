import PPAC.Migration.Internal.PacketReaderTokensSyntax

/-! Actual token Nil and Cons cases combine independent byte segmentation with real reader evaluation and exact output order. -/
namespace PPAC.Migration.Internal.PacketReaderTokensPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderTokensSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n bytes A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) :
    Derives Γ (agreement w B z o bytes A O p) := by
  have hBytes := Derives.impE (.conjL (PacketTokensBytes.nil_iff hZ w n bytes hw hn)) he
  have hRev := PacketReaderOutputOrder.nil_output hZ w A n O hw hn hOut
  exact PacketReaderTokenUnits.empty_eval_exact hZ w B z o bytes A O p hw (SyntaxNumerals.range hZ 128 w B hw hB) hz ho ha hBytes hRev

theorem cons_with_acc {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o h t n C R bytes A A1 O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) (hn : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hC : Derives Γ (PacketVarintSyntax.canonical w h C)) (hR : Derives Γ (PacketTokensBytes.encoded w t R))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C R bytes)) (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hA1 : Derives Γ (StructuralListSyntax.consCode w h A A1)) (hIH : Derives Γ (property w B z o t))
    (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) : Derives Γ (agreement w B z o bytes A O p) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hNil := StructuralNil.at_unit hZ w z o hw hz ho
  have hA1V := StructuralListValidity.cons_valid hZ w h A A1 hw hh ha hA1
  have hState : Derives Γ (PacketReaderStepSyntax.state w R z o A) := .conjI (PacketTokensBytes.output_valid w t R hR) (.conjI hzN (.conjI hoN ha))
  have hGuard : Derives Γ (PacketReaderVarintSegmentSyntax.guard o h o) := .disjL (.eqRefl o)
  have hUnit := PacketReaderTokenUnits.equation_zero_unit hZ w z o h hw hz ho hh
  have hSegment := PacketReaderVarintSegmentInduction.segment hZ w B z o h C R bytes z o A h A1 p hw hB hz hoN hC hSp hState hGuard hUnit hA1
  have hNewOut := PacketReaderOutputCons.step hZ w h A A1 o t n O hw hh hNil hA1 ht hn hOut
  have hCase := at_fields w B z o t R A1 O p hIH ht
  have hSmall := Derives.impE (Derives.impE (Derives.impE hCase hA1V) hR) hNewOut
  exact StructuralListSuffixArithmetic.iff_trans hSegment hSmall

theorem cons_with_split {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o h t n C R bytes A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) (hn : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hC : Derives Γ (PacketVarintSyntax.canonical w h C)) (hR : Derives Γ (PacketTokensBytes.encoded w t R))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C R bytes)) (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hIH : Derives Γ (property w B z o t)) (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) :
    Derives Γ (agreement w B z o bytes A O p) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc h.castSucc A.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (StructuralConsCore.exists_cons hZ w h A hw hh (StructuralListValidity.range w A ha))
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ Q
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB Q)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz Q)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho Q)
  have ht1 := of_eq (StructuralListTraceSyntax.valid_rename w t Fin.castSucc) (under ht Q)
  have hn1 := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under hn Q)
  have hC1 := of_eq (PacketVarintSyntax.canonical_rename w h C Fin.castSucc) (under hC Q)
  have hR1 := of_eq (PacketTokensBytes.encoded_rename w t R Fin.castSucc) (under hR Q)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w C R bytes Fin.castSucc) (under hSp Q)
  have ha1 := of_eq (StructuralListTraceSyntax.valid_rename w A Fin.castSucc) (under ha Q)
  have hIH1 := of_eq (property_rename w B z o t Fin.castSucc) (under hIH Q)
  have hOut1 := of_eq (PacketReaderOutputOrder.output_rename w A n O Fin.castSucc) (under hOut Q)
  simpa only [Formula.raise,agreement_rename] using cons_with_acc hZ1 w.castSucc B.castSucc z.castSucc o.castSucc h.castSucc t.castSucc n.castSucc C.castSucc R.castSucc bytes.castSucc A.castSucc (Fin.last m) O.castSucc p.castSucc hw1 hB1 hz1 ho1 (under hh Q) ht1 hn1 hC1 hR1 hSp1 ha1 (.conjR hQ) hIH1 hOut1

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o h t n bytes A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) (hn : Derives Γ (StructuralListSyntax.consCode w h t n))
    (ha : Derives Γ (StructuralListTraceSyntax.valid w A)) (hIH : Derives Γ (property w B z o t))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) :
    Derives Γ (agreement w B z o bytes A O p) := by
  have hCase := Derives.impE (.conjL (PacketTokensBytes.cons_iff hZ w h t n bytes hw hh (StructuralListValidity.range w t ht) hn)) he
  let R := PacketTokensBytes.consBody w h t bytes
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hCase
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have lift2 {φ : Formula m} (hp : Derives Γ φ) : Derives Δ (φ.rename (old 2)) := HornBinderRules.under_body 2 hp R
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (lift2 hB)
  have hz2 := of_eq (empty_rename z (old 2)) (lift2 hz)
  have ho2 := of_eq (successor_rename o z (old 2)) (lift2 ho)
  have ht2 := of_eq (StructuralListTraceSyntax.valid_rename w t (old 2)) (lift2 ht)
  have hn2 := of_eq (StructuralListSyntax.consCode_rename w h t n (old 2)) (lift2 hn)
  have ha2 := of_eq (StructuralListTraceSyntax.valid_rename w A (old 2)) (lift2 ha)
  have hIH2 := of_eq (property_rename w B z o t (old 2)) (lift2 hIH)
  have hOut2 := of_eq (PacketReaderOutputOrder.output_rename w A n O (old 2)) (lift2 hOut)
  exact of_eq (agreement_rename w B z o bytes A O p (old 2)).symm
    (cons_with_split hZ2 (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 h) (old 2 t) (old 2 n) (slot 2 0) (slot 2 1) (old 2 bytes) (old 2 A) (old 2 O) (old 2 p) hw2 hB2 hz2 ho2 (lift2 hh) ht2 hn2 (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR)) ha2 hIH2 hOut2)

end PPAC.Migration.Internal.PacketReaderTokensPoint
