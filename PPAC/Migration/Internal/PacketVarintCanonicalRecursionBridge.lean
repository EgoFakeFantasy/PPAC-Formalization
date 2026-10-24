import PPAC.Migration.Internal.PacketVarintCanonicalRecursionEquation

/-! Actual Num128 aligns the smaller canonical graph in both directions of the complete four-witness branch. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalRecursionBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintCanonicalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem large_forward {m} {Γ : Context m} (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hc : Derives Γ (largeCase false w B n s)) : Derives Γ (largeCase true w B n s) := by
  let R := largeBody false w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hp := intro_actual (old 4 w) (old 4 B) (slot 4 1) (slot 4 3) hB4 (.conjL (.conjR (.conjR (.conjR hR))))
  exact of_eq (largeCase_rename true w B n s (old 4)).symm
    (intro_large true (old 4 w) (old 4 B) (old 4 n) (old 4 s) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) hp (.conjR (.conjR (.conjR (.conjR hR)))))

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hc : Derives Γ (largeCase true w B n s)) : Derives Γ (largeCase false w B n s) := by
  let R := largeBody true w B n s
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hp := PacketVarintDomain.at_radix hZ4 (old 4 w) (old 4 B) (slot 4 1) (slot 4 3) hB4 (.conjL (.conjR (.conjR (.conjR hR))))
  exact of_eq (largeCase_rename false w B n s (old 4)).symm
    (intro_large false (old 4 w) (old 4 B) (old 4 n) (old 4 s) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
      (.conjL hR) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) hp (.conjR (.conjR (.conjR (.conjR hR)))))

theorem large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((largeCase false w B n s).iff (largeCase true w B n s)) :=
  .conjI (.impI (large_forward w B n s (add hB _) (.hyp (Or.inl rfl))))
    (.impI (large_backward (ZFContext.add hZ _) w B n s (add hB _) (.hyp (Or.inl rfl))))

theorem cases_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((atCriterion false w B n s).iff (atCriterion true w B n s)) :=
  SyntaxTypeLocalTransfer.disj_congr (SyntaxTypeLocalTransfer.iff_refl _) (large_iff hZ w B n s hB)

theorem at_actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((canonicalAt w B n s).iff (atCriterion true w B n s)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketVarintCanonicalRecursionEquation.at_iff hZ w B n s hw (SyntaxNumerals.range hZ 128 w B hw hB))
    (cases_iff hZ w B n s hB)

end PPAC.Migration.Internal.PacketVarintCanonicalRecursionBridge
