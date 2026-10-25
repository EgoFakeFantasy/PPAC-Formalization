import PPAC.Migration.Internal.PacketVarintPrefixSmall

/-! The same actual Cons aligns the shorter canonical list and the real byte tail execution. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixLarge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintPrefixRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s t a d q h x : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hd : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hq : Derives Γ (empty q).neg)
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) (hx : Derives Γ (PacketVarintSyntax.canonical w q x))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hb : Derives Γ (PacketBytesTraceSyntax.bytes w s t a)) :
    Derives Γ (largeCase w B C n t a) := by
  have hh := ZFArithmetic.add_range hZ w d B h hw (PacketAffineCore.digit_natural hZ w B d q n hw hd) hs
  have hr := PacketBytesCons.forward hZ w h x s t a hw hh (PacketVarintExecutionHelpers.list_natural w q x hx) hc hb
  let U := (PacketBytesTraceSyntax.bytes w.castSucc x.castSucc t.castSucc (Fin.last m)).conj (PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hr
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC U)
  have hd1 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under hd U)
  have hq1 : Derives Δ (empty q.castSucc).neg := by simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using under hq U
  have hs1 := of_eq (NaturalAdditionSyntax.sum_rename w d B h Fin.castSucc) (under hs U)
  have hx1 := of_eq (PacketVarintSyntax.canonical_rename w q x Fin.castSucc) (under hx U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hp := PacketVarintPrefixSyntax.intro_prefix w.castSucc q.castSucc t.castSucc (Fin.last m) x.castSucc hx1 (.conjL hU)
  have ha := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc C.castSucc h.castSucc (Fin.last m) a.castSucc hw1 hC1)) (.conjR hU)
  simpa only [Formula.raise,largeCase_rename] using intro_large w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc a.castSucc d.castSucc q.castSucc (Fin.last m) h.castSucc hd1 hq1 hs1 hp ha

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (PacketVarintCanonicalRecursionSyntax.largeCase true w B n s)) (hb : Derives Γ (PacketBytesTraceSyntax.bytes w s t a)) :
    Derives Γ (largeCase w B C n t a) := by
  let R := PacketVarintCanonicalRecursionSyntax.largeBody true w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC R)
  have hb4 := of_eq (PacketBytesTraceSyntax.bytes_rename w s t a (old 4)) (HornBinderRules.under_body 4 hb R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (largeCase_rename w B C n t a (old 4)).symm
    (point hZ4 (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 s) (old 4 t) (old 4 a) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      hw4 hC4 (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) (.conjL (.conjR (.conjR (.conjR hR)))) (.conjR (.conjR (.conjR (.conjR hR)))) hb4)

end PPAC.Migration.Internal.PacketVarintPrefixLarge
