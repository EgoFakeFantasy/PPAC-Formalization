import PPAC.Migration.Internal.PacketTokenPrefixValues

/-! Both complete actual witness blocks are eliminated, without external witnesses or standardness. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenPrefixSyntax PacketAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n B)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) :
    Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  have hsmall := Derives.impE (.conjL (PacketTokenArithmeticProperties.accepted_small_iff hZ w B C n t a hw hB hC hn)) ha
  have hc := Derives.impE (.conjL (PacketTokenArithmeticEquation.accepted_iff hZ w B C k s a hw hB hC)) hb
  apply Derives.disjE hc
  · have hk : Derives (Context.add (PacketTokenArithmeticSyntax.smallCase w B C k s a) Γ) (PacketTokenArithmeticSyntax.smallCase w B C k s a) := .hyp (Or.inl rfl)
    exact PacketDivisionUnique.unique (ZFContext.add hZ _) w C n t k s a (add hw _) (add hsmall _) (.conjR hk)
  · exact .botE (PacketTokenPrefixValues.small_large_false (ZFContext.add hZ _) w B C n t a k s
      (add hw _) (add hn _) (add hsmall _) (.hyp (Or.inl rfl)))

theorem large_cases_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t a k s : Fin m)
    (hw : Derives Γ (omega w)) (hbase : Derives Γ (affine w B d q n)) (hi : Derives Γ (property w q))
    (ha : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a))
    (hb : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C k s a)) :
    Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  let L := PacketTokenArithmeticSyntax.largeBody w B C n t a
  let ΓL := Context.add L (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ ha
  have hZ4 := HornBinderRules.zf_body 4 hZ L
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw L)
  have hbase4 := of_eq (affine_rename w B d q n (old 4)) (HornBinderRules.under_body 4 hbase L)
  have hi4 := of_eq (property_rename w q (old 4)) (HornBinderRules.under_body 4 hi L)
  have hb4 := of_eq (PacketTokenArithmeticSyntax.largeCase_rename w B C k s a (old 4)) (HornBinderRules.under_body 4 hb L)
  let M := PacketTokenArithmeticSyntax.largeBody (old 4 w) (old 4 B) (old 4 C) (old 4 k) (old 4 s) (old 4 a)
  let Δ := Context.add M (raisedContext 4 ΓL)
  apply HornBinderRules.eliminate_many 4 M _ hb4
  have hZ8 := HornBinderRules.zf_body 4 hZ4 M
  have hw8 := of_eq (omega_rename (old 4 w) (old 4)) (HornBinderRules.under_body 4 hw4 M)
  have hbase8 := of_eq (affine_rename (old 4 w) (old 4 B) (old 4 d) (old 4 q) (old 4 n) (old 4)) (HornBinderRules.under_body 4 hbase4 M)
  have hi8 := of_eq (property_rename (old 4 w) (old 4 q) (old 4)) (HornBinderRules.under_body 4 hi4 M)
  have hL : Derives ΓL L := .hyp (Or.inl rfl)
  have h0 := of_eq (affine_rename (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) (old 4)) (HornBinderRules.under_body 4 (.conjL hL) M)
  have hy := of_eq (NaturalAdditionSyntax.sum_rename (old 4 w) (slot 4 0) (old 4 B) (slot 4 3) (old 4)) (HornBinderRules.under_body 4 (.conjL (.conjR (.conjR hL))) M)
  have hu := of_eq (accepted_rename (old 4 w) (slot 4 1) (old 4 t) (slot 4 2) (old 4)) (HornBinderRules.under_body 4 (.conjL (.conjR (.conjR (.conjR hL)))) M)
  have h1 := of_eq (affine_rename (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a) (old 4)) (HornBinderRules.under_body 4 (.conjR (.conjR (.conjR (.conjR hL)))) M)
  have hM : Derives Δ M := .hyp (Or.inl rfl)
  have hpair := PacketDivisionUnique.unique hZ8 (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (old 4 d)) (old 4 (old 4 q))
    (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (old 4 n)) hw8 hbase8 h0
  have hi1 := input_subst (old 4 (old 4 w)) (old 4 (old 4 q)) (old 4 (slot 4 1)) (.conjR hpair) hi8
  exact PacketTokenPrefixValues.large_values hZ8 (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (old 4 C))
    (old 4 (old 4 n)) (old 4 (old 4 t)) (old 4 (old 4 a)) (old 4 (old 4 k)) (old 4 (old 4 s))
    (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (slot 4 2)) (old 4 (slot 4 3))
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw8 h0 (.conjL hM) hy (.conjL (.conjR (.conjR hM)))
    hu (.conjL (.conjR (.conjR (.conjR hM)))) h1 (.conjR (.conjR (.conjR (.conjR hM)))) hi1

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t a k s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hbase : Derives Γ (affine w B d q n)) (hn : Derives Γ (Formula.mem n B).neg) (hi : Derives Γ (property w q))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) :
    Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  have hl := Derives.impE (.conjL (PacketTokenArithmeticProperties.accepted_large_iff hZ w B C n t a hw hB hC hn)) ha
  have hc := Derives.impE (.conjL (PacketTokenArithmeticEquation.accepted_iff hZ w B C k s a hw hB hC)) hb
  apply Derives.disjE hc
  · have hk : Derives (Context.add (PacketTokenArithmeticSyntax.smallCase w B C k s a) Γ) (PacketTokenArithmeticSyntax.smallCase w B C k s a) := .hyp (Or.inl rfl)
    exact .botE (PacketTokenPrefixValues.small_large_false (ZFContext.add hZ _) w B C k s a n t
      (add hw _) (.conjL hk) (.conjR hk) (add hl _))
  · exact large_cases_unique (ZFContext.add hZ _) w B C n d q t a k s (add hw _) (add hbase _) (add hi _) (add hl _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketTokenPrefixPoint
