import PPAC.Migration.Internal.PacketTokenPrefixSyntax

/-! Terminal and continuation bytes are disjoint; large prefix comparison stays in the original object kernel. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixValues
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore PacketTokenAcceptedSyntax
open PacketTokenPrefixSyntax
open NaturalAdditionSyntax (sum)

theorem shifted_not_small {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hs : Derives Γ (sum w d B y)) :
    Derives Γ (Formula.mem y B).neg := by
  apply Derives.impI
  have hB := radix_guard _ _ _ _ _ ha
  have hd := digit_natural hZ w B d q n hw ha
  have hl := GodelPairArithmetic.sum_right_bound hZ w d B y hw hd hB hs
  exact NaturalOrderBasic.below_not_reverse (ZFContext.add hZ _) w B y (add hw _) (add hB _) (add hl _) (.hyp (Or.inl rfl))

theorem small_large_false {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n B)) (ha : Derives Γ (affine w C n t a))
    (hl : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C k s a)) : Derives Γ .bot := by
  let L := PacketTokenArithmeticSyntax.largeBody w B C k s a
  let Δ := Context.add L (HornBinderSyntax.raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ hl
  have hZ4 := HornBinderRules.zf_body 4 hZ L
  have hw4 := SyntaxRenameQuerySyntax.of_eq (omega_rename w (HornBinderSyntax.old 4)) (HornBinderRules.under_body 4 hw L)
  have hn4 : Derives Δ (.mem (HornBinderSyntax.old 4 n) (HornBinderSyntax.old 4 B)) := HornBinderRules.under_body 4 hn L
  have ha4 := SyntaxRenameQuerySyntax.of_eq (affine_rename w C n t a (HornBinderSyntax.old 4)) (HornBinderRules.under_body 4 ha L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have he := PacketDivisionUnique.unique hZ4 (HornBinderSyntax.old 4 w) (HornBinderSyntax.old 4 C)
    (HornBinderSyntax.old 4 n) (HornBinderSyntax.old 4 t) (HornBinderSyntax.slot 4 3) (HornBinderSyntax.slot 4 2)
    (HornBinderSyntax.old 4 a) hw4 ha4 (.conjR (.conjR (.conjR (.conjR hL))))
  have hno := shifted_not_small hZ4 (HornBinderSyntax.old 4 w) (HornBinderSyntax.old 4 B)
    (HornBinderSyntax.slot 4 0) (HornBinderSyntax.slot 4 1) (HornBinderSyntax.old 4 k) (HornBinderSyntax.slot 4 3)
    hw4 (.conjL hL) (.conjL (.conjR (.conjR hL)))
  exact .impE hno (mem_subst (.conjL he) hn4)

theorem large_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a k s d q u y e p v z : Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (affine w B d q n)) (h2 : Derives Γ (affine w B e p k))
    (hy : Derives Γ (sum w d B y)) (hz : Derives Γ (sum w e B z))
    (hu : Derives Γ (accepted w q t u)) (hv : Derives Γ (accepted w p s v))
    (h1 : Derives Γ (affine w C y u a)) (h3 : Derives Γ (affine w C z v a)) (hi : Derives Γ (property w q)) :
    Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  have hp := PacketDivisionUnique.unique hZ w C y u z v a hw h1 h3
  have hvu := PacketTokenPrefixTransport.accepted_output w p s v u (eq_symm (.conjR hp)) hv
  have hqs := property_at w q t u p s hi hu hvu
  have hzy := PacketTokenPrefixTransport.sum_output w e B z y (eq_symm (.conjL hp)) hz
  have hd := digit_natural hZ w B d q n hw h0
  have he := digit_natural hZ w B e p k hw h2
  have hB := radix_guard _ _ _ _ _ h0
  have hys := ZFArithmetic.add_commute hZ w d B y hw hd hB hy
  have hzs := ZFArithmetic.add_commute hZ w e B y hw he hB hzy
  have hde := GodelPairArithmetic.cancel_sum_left hZ w B d e y hw hB hd he hys hzs
  have h0e := PacketAffineTransport.digit w B d q n e hde h0
  have h0p := PacketAffineTransport.tail w B e q n p (.conjL hqs) h0e
  exact .conjI (PacketAffineCore.unique hZ w B e p n k hw h0p h2) (.conjR hqs)

end PPAC.Migration.Internal.PacketTokenPrefixValues
