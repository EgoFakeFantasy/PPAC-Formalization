import PPAC.Migration.Internal.PacketReaderVarintSegmentSmall
import PPAC.Migration.Internal.PacketReaderVarintSegmentContinue

/-! Actual canonical small/large cases yield complete segment consumption, with the real smaller-token property and no external recursion. -/
namespace PPAC.Migration.Internal.PacketReaderVarintSegmentCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderVarintSegmentSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem large_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T L v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (earlier w B z o n)) (hLarge : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L)) (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a))
    (hu : Derives Γ (PacketAffineSyntax.equation w n v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ (agreement w B z o L T v s a c p) := by
  let R := PacketVarintCanonicalRecursionSyntax.largeBody true w B n C
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hLarge
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz R)
  have ho4 : Derives Δ (.mem (old 4 o) (old 4 w)) := HornBinderRules.under_body 4 ho R
  have hi4 := of_eq (earlier_rename w B z o n (old 4)) (HornBinderRules.under_body 4 hi R)
  have hSp4 := of_eq (StructuralListSpliceSyntax.splice_rename w C T L (old 4)) (HornBinderRules.under_body 4 hSp R)
  have hT4 := of_eq (PacketReaderStepSyntax.state_rename w T v s a (old 4)) (HornBinderRules.under_body 4 hT R)
  have hu4 := of_eq (PacketAffineSyntax.equation_rename w n v s u (old 4)) (HornBinderRules.under_body 4 hu R)
  have hc4 := of_eq (StructuralListSyntax.consCode_rename w u a c (old 4)) (HornBinderRules.under_body 4 hc R)
  have hAff := Derives.conjL hR
  have hKN := PacketAffineCore.tail_guard _ _ _ _ _ hAff
  have hNotZero := Derives.conjL (.conjR hR)
  have hSum := Derives.conjL (.conjR (.conjR hR))
  have hCanonical := Derives.conjL (.conjR (.conjR (.conjR hR)))
  have hCons := Derives.conjR (.conjR (.conjR (.conjR hR)))
  have hBelow := Derives.impE (.conjR (PacketDivisionDescentCore.quotient_bounds hZ4 false (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) hw4 hB4 hAff)) hNotZero
  have hIH := earlier_at (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 1) hi4 hKN hBelow
  have hHN := ZFArithmetic.add_range hZ4 _ _ _ _ hw4 (PacketAffineCore.digit_natural hZ4 _ _ _ _ _ hw4 hAff) hSum
  have hXN := PacketVarintExecutionHelpers.list_natural (old 4 w) (slot 4 1) (slot 4 3) hCanonical
  have hRem := StructuralListSplice.cons_forward hZ4 (old 4 w) (slot 4 2) (slot 4 3) (old 4 C) (old 4 T) (old 4 L) hw4 hHN hXN hCons hSp4
  let S := (StructuralListSpliceSyntax.splice (old 4 w).castSucc (slot 4 3).castSucc (old 4 T).castSucc (Fin.last (m+4))).conj
    (StructuralListSyntax.consCode (old 4 w).castSucc (slot 4 2).castSucc (Fin.last (m+4)) (old 4 L).castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hRem
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ5 := ZFContext.under hZ4 S
  have hw5 := of_eq (omega_rename (old 4 w) Fin.castSucc) (under hw4 S)
  have hz5 := of_eq (empty_rename (old 4 z) Fin.castSucc) (under hz4 S)
  have hAff5 := of_eq (PacketAffineSyntax.affine_rename (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) Fin.castSucc) (under hAff S)
  have hk5 : Derives Ξ (empty (slot 4 1).castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hNotZero S
  have hSum5 := of_eq (NaturalAdditionSyntax.sum_rename (old 4 w) (slot 4 0) (old 4 B) (slot 4 2) Fin.castSucc) (under hSum S)
  have hCanon5 := of_eq (PacketVarintSyntax.canonical_rename (old 4 w) (slot 4 1) (slot 4 3) Fin.castSucc) (under hCanonical S)
  have hT5 := of_eq (PacketReaderStepSyntax.state_rename (old 4 w) (old 4 T) (old 4 v) (old 4 s) (old 4 a) Fin.castSucc) (under hT4 S)
  have hu5 := of_eq (PacketAffineSyntax.equation_rename (old 4 w) (old 4 n) (old 4 v) (old 4 s) (old 4 u) Fin.castSucc) (under hu4 S)
  have hc5 := of_eq (StructuralListSyntax.consCode_rename (old 4 w) (old 4 u) (old 4 a) (old 4 c) Fin.castSucc) (under hc4 S)
  have hIH5 := of_eq (property_rename (old 4 w) (old 4 B) (old 4 z) (old 4 o) (slot 4 1) Fin.castSucc) (under hIH S)
  have hBN := SyntaxNumerals.range hZ4 128 (old 4 w) (old 4 B) hw4 hB4
  have hout := PacketReaderVarintSegmentContinue.point hZ5 (old 4 w).castSucc (old 4 B).castSucc (old 4 z).castSucc (old 4 o).castSucc (old 4 n).castSucc (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc (Fin.last (m+4)) (old 4 T).castSucc (old 4 L).castSucc (old 4 v).castSucc (old 4 s).castSucc (old 4 a).castSucc (old 4 u).castSucc (old 4 c).castSucc (old 4 p).castSucc
    hw5 (under hBN S) hz5 (under ho4 S) hAff5 hk5 hSum5 hCanon5 (.conjL hS) (.conjR hS) hT5 hu5 hc5 hIH5
  simpa only [Formula.raise,agreement_rename] using hout

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T L v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (earlier w B z o n)) (hCanonical : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L)) (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a))
    (hG : Derives Γ (guard o n s)) (hu : Derives Γ (PacketAffineSyntax.equation w n v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ (agreement w B z o L T v s a c p) := by
  apply Derives.disjE (PacketVarintExecutionHelpers.cases_at hZ w B n C hw hB hCanonical)
  · have hSmall : Derives (Context.add (PacketVarintCanonicalRecursionSyntax.smallCase w B n C) Γ) (PacketVarintCanonicalRecursionSyntax.smallCase w B n C) := .hyp (Or.inl rfl)
    exact PacketReaderVarintSegmentSmall.small (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (add hw _) (add (SyntaxNumerals.range hZ 128 w B hw hB) _) (add hz _) (add ho _) (.conjL hSmall) (.conjR hSmall) (add hSp _) (add hT _) (add hG _) (add hu _) (add hc _)
  · exact large_case (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (add hi _) (.hyp (Or.inl rfl)) (add hSp _) (add hT _) (add hu _) (add hc _)

end PPAC.Migration.Internal.PacketReaderVarintSegmentCases
