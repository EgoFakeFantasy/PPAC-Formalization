import PPAC.Migration.Internal.PacketVarintExecutionTotal

/-! Every actual canonical candidate has the independent full-Fields ByteList input guard. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionDomain
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketByteInputSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (PacketVarintCanonicalRecursionSyntax.smallCase w B n s)) : Derives Γ (byteList w s) := by
  have hb := intro_byte C n hC (PacketTokenByteBounds.small_digit_byte hZ w B C n hw hB hC (.conjL hc))
  let E := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) s.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR hc)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hb1 := of_eq (byte_rename n Fin.castSucc) (under hb E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have he := PacketVarintExecutionHelpers.nil_input hZ1 w.castSucc (Fin.last m) hw1 (.conjL hE)
  simpa only [Formula.raise,byteList_rename] using PacketVarintExecutionHelpers.cons_input hZ1 w.castSucc s.castSucc n.castSucc (Fin.last m) hw1 (.conjR hE) hb1 he

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s d q h x : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hq : Derives Γ (empty q).neg)
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) (hp : Derives Γ (canonical w q x)) (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) : Derives Γ (byteList w s) := by
  have hP := PacketVarintExecutionHelpers.below_property hZ w B n d q hw hB hi ha hq
  have hx := domain_at w q x hP hp
  have hh := intro_byte C h hC (PacketTokenByteBounds.shifted_digit_byte hZ w B C d h hw hB hC (PacketAffineCore.digit_guard _ _ _ _ _ ha) hs)
  exact PacketVarintExecutionHelpers.cons_input hZ w s h x hw hc hh hx

theorem large_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) (hc : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n s)) : Derives Γ (byteList w s) := by
  let R := PacketVarintCanonicalRecursionSyntax.largeBody true w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC R)
  have hi4 := of_eq (earlier_rename w n (old 4)) (HornBinderRules.under_body 4 hi R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (byteList_rename w s (old 4)).symm (large_point hZ4 (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 s) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    hw4 hB4 hC4 hi4 (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) (.conjL (.conjR (.conjR (.conjR hR)))) (.conjR (.conjR (.conjR (.conjR hR)))))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) (hc : Derives Γ (canonical w n s)) : Derives Γ (byteList w s) := by
  apply Derives.disjE (PacketVarintExecutionHelpers.cases_at hZ w B n s hw hB hc)
  · exact small_point (ZFContext.add hZ _) w B C n s (add hw _) (add hB _) (add hC _) (.hyp (Or.inl rfl))
  · exact large_case (ZFContext.add hZ _) w B C n s (add hw _) (add hB _) (add hC _) (add hi _) (.hyp (Or.inl rfl))

theorem domain_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) : Derives Γ (domain w n) := by
  apply Derives.allI
  apply Derives.impI
  let H := canonical w.castSucc n.castSucc (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB H)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC H)
  have hi1 := of_eq (earlier_rename w n Fin.castSucc) (under hi H)
  exact point hZ1 w.castSucc B.castSucc C.castSucc n.castSucc (Fin.last m) hw1 hB1 hC1 hi1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketVarintExecutionDomain
