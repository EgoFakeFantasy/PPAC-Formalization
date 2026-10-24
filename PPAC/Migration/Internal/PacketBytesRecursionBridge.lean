import PPAC.Migration.Internal.PacketBytesRecursionEquation

/-! The exact radix criterion and the independent actual-byte criterion are object-equivalent. -/
namespace PPAC.Migration.Internal.PacketBytesRecursionBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_to_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (consCase w C n t a)) :
    Derives Γ (actualCons w n t a) := by
  let R := consBody w C n t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_body 3 hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb := intro_bytes (old 3 w) (old 3 C) (slot 3 1) (old 3 t) (slot 3 2) hC3 (.conjL (.conjR hR))
  have ha := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff hZ3 true (old 3 w) (old 3 C) (slot 3 0) (slot 3 2) (old 3 a) hw3 hC3)) (.conjR (.conjR hR))
  exact of_eq (actualCons_rename w n t a (old 3)).symm
    (intro_actual (old 3 w) (old 3 n) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2) (.conjL hR) hb ha)

theorem actual_to_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (actualCons w n t a)) :
    Derives Γ (consCase w C n t a) := by
  let R := actualBody w n t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_body 3 hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hf := PacketBytesLaws.fold_at hZ3 (old 3 w) (old 3 C) (slot 3 1) (old 3 t) (slot 3 2) hC3 (.conjL (.conjR hR))
  have ha := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ3 true (old 3 w) (old 3 C) (slot 3 0) (slot 3 2) (old 3 a) hw3 hC3)) (.conjR (.conjR hR))
  exact of_eq (consCase_rename w C n t a (old 3)).symm
    (intro_cons (old 3 w) (old 3 C) (old 3 n) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2) (.conjL hR) hf ha)

theorem to_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (caseAt w C n t a)) :
    Derives Γ (criterion w n t a) := by
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (cons_to_actual (ZFContext.add hZ _) w C n t a (add hw _) (add hC _) (.hyp (Or.inl rfl)))

theorem from_actual {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hc : Derives Γ (criterion w n t a)) :
    Derives Γ (caseAt w C n t a) := by
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (actual_to_cons (ZFContext.add hZ _) w C n t a (add hw _) (add hC _) (.hyp (Or.inl rfl)))

theorem cases_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((caseAt w C n t a).iff (criterion w n t a)) :=
  .conjI (.impI (to_actual (ZFContext.add hZ _) w C n t a (add hw _) (add hC _) (.hyp (Or.inl rfl))))
    (.impI (from_actual (ZFContext.add hZ _) w C n t a (add hw _) (add hC _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PacketBytesRecursionBridge
