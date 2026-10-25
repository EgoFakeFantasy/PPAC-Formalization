import PPAC.Migration.Internal.PacketTokenCanonicalSyntax

/-! Real quotient descent authorizes the smaller agreement and every original arithmetic witness remains exact. -/
namespace PPAC.Migration.Internal.PacketTokenCanonicalStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenCanonicalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem below_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n d q t u : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hq : Derives Γ (empty q).neg) : Derives Γ (agreement w q t u) := by
  have hqn := Derives.impE (.conjR (PacketDivisionDescentCore.quotient_bounds hZ false w B d q n hw hB ha)) hq
  exact property_at w q t u (earlier_at w n q hi (PacketAffineCore.tail_guard _ _ _ _ _ ha) hqn)

theorem large_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (hc : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a)) : Derives Γ (PacketVarintPrefixRecursionSyntax.largeCase w B C n t a) := by
  let R := PacketTokenArithmeticSyntax.largeBody w B C n t a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hi4 := of_eq (earlier_rename w n (old 4)) (HornBinderRules.under_body 4 hi R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := below_agreement hZ4 (old 4 w) (old 4 B) (old 4 n) (slot 4 0) (slot 4 1) (old 4 t) (slot 4 2) hw4 hB4 hi4 (.conjL hR) (.conjL (.conjR hR))
  have hp := Derives.impE (.conjL he) (.conjL (.conjR (.conjR (.conjR hR))))
  exact of_eq (PacketVarintPrefixRecursionSyntax.largeCase_rename w B C n t a (old 4)).symm
    (PacketVarintPrefixRecursionSyntax.intro_large (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 t) (old 4 a) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) hp (.conjR (.conjR (.conjR (.conjR hR)))))

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (hc : Derives Γ (PacketVarintPrefixRecursionSyntax.largeCase w B C n t a)) : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a) := by
  let R := PacketVarintPrefixRecursionSyntax.largeBody w B C n t a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hi4 := of_eq (earlier_rename w n (old 4)) (HornBinderRules.under_body 4 hi R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := below_agreement hZ4 (old 4 w) (old 4 B) (old 4 n) (slot 4 0) (slot 4 1) (old 4 t) (slot 4 2) hw4 hB4 hi4 (.conjL hR) (.conjL (.conjR hR))
  have hp := Derives.impE (.conjR he) (.conjL (.conjR (.conjR (.conjR hR))))
  exact of_eq (PacketTokenArithmeticSyntax.largeCase_rename w B C n t a (old 4)).symm
    (PacketTokenArithmeticSyntax.intro_large (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 t) (old 4 a) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) hp (.conjR (.conjR (.conjR (.conjR hR)))))

theorem criterion_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n)) :
    Derives Γ ((PacketTokenArithmeticSyntax.criterion w B C n t a).iff (PacketVarintPrefixRecursionSyntax.criterion w B C n t a)) :=
  SyntaxTypeLocalTransfer.disj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (.conjI (.impI (large_forward (ZFContext.add hZ _) w B C n t a (add hw _) (add hB _) (add hi _) (.hyp (Or.inl rfl))))
      (.impI (large_backward (ZFContext.add hZ _) w B C n t a (add hw _) (add hB _) (add hi _) (.hyp (Or.inl rfl)))))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) : Derives Γ (agreement w n t a) := by
  have h0 := PacketTokenArithmeticEquation.accepted_iff hZ w B C n t a hw hB hC
  have h1 := criterion_iff hZ w B C n t a hw hB hi
  have h2 := PacketVarintPrefixEquation.prefix_iff hZ w B C n t a hw hB hC
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans h0 h1) (.conjI (.conjR h2) (.conjL h2))

theorem property_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_many 2 hB)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_many 2 hC)
  have hi2 := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_many 2 hi)
  exact point (HornBinderRules.zf_many 2 hZ) (old 2 w) (old 2 B) (old 2 C) (old 2 n) (slot 2 0) (slot 2 1) hw2 hB2 hC2 hi2

end PPAC.Migration.Internal.PacketTokenCanonicalStep
