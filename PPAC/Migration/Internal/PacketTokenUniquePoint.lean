import PPAC.Migration.Internal.PacketTokenUniqueValues

/-! Both actual large witness blocks are eliminated before the recursive output comparison. -/
namespace PPAC.Migration.Internal.PacketTokenUniquePoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenUniqueSyntax PacketAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n B)) (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w n t b)) : Derives Γ (.equal a b) :=
  PacketAffineCore.unique hZ w C n t a b hw
    (.impE (.conjL (PacketTokenArithmeticProperties.accepted_small_iff hZ w B C n t a hw hB hC hn)) ha)
    (.impE (.conjL (PacketTokenArithmeticProperties.accepted_small_iff hZ w B C n t b hw hB hC hn)) hb)

theorem large_cases_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t a b : Fin m)
    (hw : Derives Γ (omega w)) (hbase : Derives Γ (affine w B d q n)) (hi : Derives Γ (property w q))
    (ha : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a))
    (hb : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t b)) : Derives Γ (.equal a b) := by
  let L := PacketTokenArithmeticSyntax.largeBody w B C n t a
  let ΓL := Context.add L (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 L _ ha
  have hZ4 := HornBinderRules.zf_body 4 hZ L
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw L)
  have hbase4 := of_eq (affine_rename w B d q n (old 4)) (HornBinderRules.under_body 4 hbase L)
  have hi4 := of_eq (property_rename w q (old 4)) (HornBinderRules.under_body 4 hi L)
  have hb4 := of_eq (PacketTokenArithmeticSyntax.largeCase_rename w B C n t b (old 4)) (HornBinderRules.under_body 4 hb L)
  let M := PacketTokenArithmeticSyntax.largeBody (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 t) (old 4 b)
  let Δ := Context.add M (raisedContext 4 ΓL)
  apply HornBinderRules.eliminate_many 4 M _ hb4
  have hZ8 := HornBinderRules.zf_body 4 hZ4 M
  have hw8 := of_eq (omega_rename (old 4 w) (old 4)) (HornBinderRules.under_body 4 hw4 M)
  have hbase8 := of_eq (affine_rename (old 4 w) (old 4 B) (old 4 d) (old 4 q) (old 4 n) (old 4)) (HornBinderRules.under_body 4 hbase4 M)
  have hi8 := of_eq (property_rename (old 4 w) (old 4 q) (old 4)) (HornBinderRules.under_body 4 hi4 M)
  have hL : Derives ΓL L := .hyp (Or.inl rfl)
  have hL8 : Derives Δ
      ((affine (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (old 4 n))).conj
        ((empty (old 4 (slot 4 1))).neg.conj
          ((NaturalAdditionSyntax.sum (old 4 (old 4 w)) (old 4 (slot 4 0)) (old 4 (old 4 B)) (old 4 (slot 4 3))).conj
            ((accepted (old 4 (old 4 w)) (old 4 (slot 4 1)) (old 4 (old 4 t)) (old 4 (slot 4 2))).conj
              (affine (old 4 (old 4 w)) (old 4 (old 4 C)) (old 4 (slot 4 3)) (old 4 (slot 4 2)) (old 4 (old 4 a))))))) :=
    of_eq (by simp only [L,PacketTokenArithmeticSyntax.largeBody,Formula.rename,affine_rename,empty_rename,
      NaturalAdditionSyntax.sum_rename,accepted_rename]) (HornBinderRules.under_body 4 hL M)
  have hM : Derives Δ M := .hyp (Or.inl rfl)
  have hpair := PacketDivisionUnique.unique hZ8 (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (old 4 d)) (old 4 (old 4 q))
    (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (old 4 n)) hw8 hbase8 (.conjL hL8)
  have hi1 := input_subst (old 4 (old 4 w)) (old 4 (old 4 q)) (old 4 (slot 4 1)) (.conjR hpair) hi8
  exact PacketTokenUniqueValues.unique hZ8 (old 4 (old 4 w)) (old 4 (old 4 B)) (old 4 (old 4 C)) (old 4 (old 4 n)) (old 4 (old 4 t))
    (old 4 (old 4 a)) (old 4 (old 4 b)) (old 4 (slot 4 0)) (old 4 (slot 4 1)) (old 4 (slot 4 2)) (old 4 (slot 4 3))
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw8 (.conjL hL8) (.conjL hM)
    (.conjL (.conjR (.conjR hL8))) (.conjL (.conjR (.conjR hM)))
    (.conjL (.conjR (.conjR (.conjR hL8)))) (.conjL (.conjR (.conjR (.conjR hM))))
    (.conjR (.conjR (.conjR (.conjR hL8)))) (.conjR (.conjR (.conjR (.conjR hM)))) hi1

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t a b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hbase : Derives Γ (affine w B d q n)) (hn : Derives Γ (Formula.mem n B).neg) (hi : Derives Γ (property w q))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w n t b)) : Derives Γ (.equal a b) :=
  large_cases_unique hZ w B C n d q t a b hw hbase hi
    (.impE (.conjL (PacketTokenArithmeticProperties.accepted_large_iff hZ w B C n t a hw hB hC hn)) ha)
    (.impE (.conjL (PacketTokenArithmeticProperties.accepted_large_iff hZ w B C n t b hw hB hC hn)) hb)

end PPAC.Migration.Internal.PacketTokenUniquePoint
