import PPAC.Migration.Internal.PacketTokenApplicationSyntax

/-! Original bounded applications are exactly the complete token outcomes, with all search bounds discharged. -/
namespace PPAC.Migration.Internal.PacketTokenApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketTokenRuleData PacketTokenSyntax PacketTokenApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (ha : Derives Γ (HornApplicationSyntax.application smallRule w r V)) : Derives Γ (smallOutcome w B V r) := by
  let L := HornApplicationSyntax.body smallRule w r V
  let Δ := Context.add L (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application smallRule w r V _ ha
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw L)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_body 3 hB L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hs := Derives.impE (.conjL (PacketTokenMatrix.small_at (HornBinderRules.zf_body 3 hZ L)
    (old 3 w) (old 3 B) (old 3 r) (old 3 V) (slot 3) hw3 (.conjL hL) hB3)) (.conjR (.conjR hL))
  exact of_eq (smallOutcome_rename w B V r (old 3)).symm
    (intro_small (old 3 w) (old 3 B) (old 3 V) (old 3 r) (slot 3 0) (slot 3 1) (slot 3 2) hs)

theorem small_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hs : Derives Γ (smallOutcome w B V r)) : Derives Γ (HornApplicationSyntax.application smallRule w r V) := by
  let L := smallBody w B V r
  let Δ := Context.add L (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 L _ hs
  have hZ3 := HornBinderRules.zf_body 3 hZ L
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw L)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_body 3 hB L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  let env := SyntaxAtomSyntax.three (slot 3 0 : Fin (m+3)) (slot 3 1) (slot 3 2)
  have hn := PacketTokenNatural.row_environment hZ3 2 (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r) hw3 (.conjL hL)
  have hb := PacketTokenApplicationBounds.row_bounds hZ3 2 (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r) hw3 (.conjL hL)
  have hm := Derives.impE (.conjR (PacketTokenMatrix.small_at hZ3 (old 3 w) (old 3 B) (old 3 r) (old 3 V) env hw3 hn hB3)) hL
  exact of_eq (HornApplicationSyntax.application_rename smallRule w r V (old 3)).symm
    (HornApplicationRules.intro_application smallRule (old 3 w) (old 3 r) (old 3 V) env hn hb hm)

theorem small_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((HornApplicationSyntax.application smallRule w r V).iff (smallOutcome w B V r)) := by
  apply Derives.conjI
  · exact .impI (small_forward (ZFContext.add hZ _) w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (small_backward (ZFContext.add hZ _) w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))

theorem large_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (ha : Derives Γ (HornApplicationSyntax.application largeRule w r V)) : Derives Γ (largeOutcome w B V r) := by
  let L := HornApplicationSyntax.body largeRule w r V
  let Δ := Context.add L (raisedContext 6 Γ)
  apply HornApplicationRules.eliminate_application largeRule w r V _ ha
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw L)
  have hB6 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 6)) (HornBinderRules.under_body 6 hB L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hl := PacketTokenLocal.large_forward (HornBinderRules.zf_body 6 hZ L) (old 6 w) (old 6 B) (old 6 r) (old 6 V) (slot 6)
    hw6 (.conjL hL) hB6 (.conjR (.conjR hL))
  exact of_eq (largeOutcome_rename w B V r (old 6)).symm (intro_large (old 6 w) (old 6 B) (old 6 V) (old 6 r) (slot 6) hl)

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hl : Derives Γ (largeOutcome w B V r)) : Derives Γ (HornApplicationSyntax.application largeRule w r V) := by
  let L := largeOutcomeBody w B V r
  let Δ := Context.add L (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 L _ hl
  have hZ6 := HornBinderRules.zf_body 6 hZ L
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw L)
  have hB6 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 6)) (HornBinderRules.under_body 6 hB L)
  have hC6 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 6)) (HornBinderRules.under_body 6 hC L)
  have hv6 := of_eq (PacketTraceCore.value_rename w V (old 6)) (HornBinderRules.under_body 6 hv L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hn := PacketTokenNatural.large_environment hZ6 (old 6 w) (old 6 B) (old 6 V) (old 6 r) (slot 6) hw6 hL
  have hb := PacketTokenApplicationBounds.large_bounds hZ6 (old 6 w) (old 6 B) (old 6 C) (old 6 V) (old 6 r) (slot 6) hw6 hB6 hC6 hv6 hL
  have hm := PacketTokenLocal.large_backward hZ6 (old 6 w) (old 6 B) (old 6 r) (old 6 V) (slot 6) hw6 hn hB6 hL
  exact of_eq (HornApplicationSyntax.application_rename largeRule w r V (old 6)).symm
    (HornApplicationRules.intro_application largeRule (old 6 w) (old 6 r) (old 6 V) (slot 6) hn hb hm)

theorem large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((HornApplicationSyntax.application largeRule w r V).iff (largeOutcome w B V r)) := by
  apply Derives.conjI
  · exact .impI (large_forward (ZFContext.add hZ _) w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (large_backward (ZFContext.add hZ _) w B C r V (add hw _) (add hB _) (add hC _) (add hv _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenApplication
