import PPAC.Migration.Internal.PacketVarintPrefixLarge

/-! Independent Prefix has the exact terminal/continuation arithmetic recurrence on all internal candidates. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixEquation
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintPrefixSyntax PacketVarintPrefixRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hp : Derives Γ (prefixCode w n t a)) : Derives Γ (criterion w B C n t a) := by
  let R := PacketVarintPrefixSyntax.body w n t a
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hp
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := PacketVarintExecutionHelpers.cases_at hZ1 w.castSucc B.castSucc n.castSucc (Fin.last m) hw1 hB1 (.conjL hR)
  apply of_eq (criterion_rename w B C n t a Fin.castSucc).symm
  apply Derives.disjE he
  · exact .disjL (PacketVarintPrefixSmall.forward (ZFContext.add hZ1 _) w.castSucc B.castSucc C.castSucc n.castSucc (Fin.last m) t.castSucc a.castSucc (add hw1 _) (add hB1 _) (add hC1 _) (.hyp (Or.inl rfl)) (add (.conjR hR) _))
  · exact .disjR (PacketVarintPrefixLarge.forward (ZFContext.add hZ1 _) w.castSucc B.castSucc C.castSucc n.castSucc (Fin.last m) t.castSucc a.castSucc (add hw1 _) (add hC1 _) (.hyp (Or.inl rfl)) (add (.conjR hR) _))

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (largeCase w B C n t a)) : Derives Γ (prefixCode w n t a) := by
  let R := largeBody w B C n t a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB R)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff hZ4 true (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a) hw4 hC4)) (.conjR (.conjR (.conjR (.conjR hR))))
  exact of_eq (prefixCode_rename w n t a (old 4)).symm
    (PacketVarintPrefixConstruct.continuation hZ4 (old 4 w) (old 4 B) (slot 4 1) (old 4 t) (slot 4 2) (slot 4 0) (slot 4 3) (old 4 n) (old 4 a)
      hw4 hB4 (.conjL (.conjR hR)) (.conjL (.conjR (.conjR (.conjR hR)))) (.conjL hR) (.conjL (.conjR (.conjR hR))) ha)

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (criterion w B C n t a)) : Derives Γ (prefixCode w n t a) := by
  apply Derives.disjE hc
  · have hS : Derives (Context.add (smallCase w B C n t a) Γ) (smallCase w B C n t a) := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ (smallCase w B C n t a)
    have ha := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff hZ1 true w C n t a (add hw _) (add hC _))) (.conjR hS)
    exact PacketVarintPrefixConstruct.terminal hZ1 w B n t a (add hw _) (add hB _) (.conjL hS) ha
  · exact large_backward (ZFContext.add hZ _) w B C n t a (add hw _) (add hB _) (add hC _) (.hyp (Or.inl rfl))

theorem prefix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((prefixCode w n t a).iff (criterion w B C n t a)) :=
  .conjI (.impI (forward (ZFContext.add hZ _) w B C n t a (add hw _) (add hB _) (add hC _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w B C n t a (add hw _) (add hB _) (add hC _) (.hyp (Or.inl rfl))))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) : Derives Γ (allLaw w B C) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_many 3 hB)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_many 3 hC)
  exact prefix_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (old 3 B) (old 3 C) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 hC3

end PPAC.Migration.Internal.PacketVarintPrefixEquation
