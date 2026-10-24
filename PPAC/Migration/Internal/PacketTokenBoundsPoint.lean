import PPAC.Migration.Internal.PacketTokenBoundsSyntax

/-! Actual token branches preserve both input and tail bounds through their real recursive run. -/
namespace PPAC.Migration.Internal.PacketTokenBoundsPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenBoundsSyntax PacketAffineSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n B)) (ha : Derives Γ (accepted w n t a)) : Derives Γ (bounds n t a) := by
  have hA := Derives.impE (.conjL (PacketTokenArithmeticProperties.accepted_small_iff hZ w B C n t a hw hB hC hn)) ha
  exact .conjI (PacketTokenEntryArithmetic.digit_below_output hZ w C n t a hw hA)
    (PacketDivisionDescentCore.quotient_below hZ true w C n t a hw hC hA)

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hbase : Derives Γ (affine w B d q n)) (hn : Derives Γ (Formula.mem n B).neg) (hi : Derives Γ (property w q))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (bounds n t a) := by
  have hl := Derives.impE (.conjL (PacketTokenArithmeticProperties.accepted_large_iff hZ w B C n t a hw hB hC hn)) ha
  let L := PacketTokenArithmeticSyntax.largeBody w B C n t a
  let Δ := Context.add L (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ hl
  have hZ4 := HornBinderRules.zf_body 4 hZ L
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw L)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB L)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC L)
  have hbase4 := of_eq (affine_rename w B d q n (old 4)) (HornBinderRules.under_body 4 hbase L)
  have hi4 := of_eq (property_rename w q (old 4)) (HornBinderRules.under_body 4 hi L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have h0 := Derives.conjL hL
  have hs := Derives.conjL (.conjR (.conjR hL))
  have ht := Derives.conjL (.conjR (.conjR (.conjR hL)))
  have h1 := Derives.conjR (.conjR (.conjR (.conjR hL)))
  have hpair := PacketDivisionUnique.unique hZ4 (old 4 w) (old 4 B) (old 4 d) (old 4 q) (slot 4 0) (slot 4 1) (old 4 n) hw4 hbase4 h0
  have hi1 := input_subst (old 4 w) (old 4 q) (slot 4 1) (.conjR hpair) hi4
  have hb := property_at (old 4 w) (slot 4 1) (old 4 t) (slot 4 2) hi1 ht
  have hBC : Derives Δ (below (old 4 B) (old 4 C)) := .disjR (SyntaxNumerals.less hZ4 128 256 (by decide) _ _ hB4 hC4)
  have hdy := GodelPairArithmetic.sum_left_bound hZ4 (old 4 w) (slot 4 0) (old 4 B) (slot 4 3) hw4
    (PacketAffineCore.digit_natural hZ4 _ _ _ _ _ hw4 h0) (PacketAffineCore.radix_guard _ _ _ _ _ h0) hs
  have hna := PacketTokenBoundComparison.affine_compare hZ4 (old 4 w) (old 4 B) (old 4 C) (slot 4 0) (slot 4 1) (old 4 n)
    (slot 4 3) (slot 4 2) (old 4 a) hw4 h0 h1 hBC hdy (.conjL hb)
  have hua := PacketDivisionDescentCore.quotient_below hZ4 true (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a) hw4 hC4 h1
  have hta := NaturalOrderBasic.transitive hZ4 (old 4 w) (old 4 t) (slot 4 2) (old 4 a) hw4 (PacketAffineCore.output_guard _ _ _ _ _ h1) (.conjR hb) hua
  exact of_eq (bounds_rename n t a (old 4)).symm (.conjI hna hta)

end PPAC.Migration.Internal.PacketTokenBoundsPoint
