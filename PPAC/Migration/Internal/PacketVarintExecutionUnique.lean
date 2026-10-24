import PPAC.Migration.Internal.PacketVarintExecutionUniqueCases

/-! Exact canonical recursion and all four branch combinations prove arbitrary-candidate list uniqueness. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n))
    (hs : Derives Γ (canonical w n s)) (ht : Derives Γ (canonical w n t)) : Derives Γ (.equal s t) := by
  apply Derives.disjE (PacketVarintExecutionHelpers.cases_at hZ w B n s hw hB hs)
  · let A := PacketVarintCanonicalRecursionSyntax.smallCase w B n s
    have hZ1 := ZFContext.add hZ A
    have hA : Derives (Context.add A Γ) A := .hyp (Or.inl rfl)
    apply Derives.disjE (PacketVarintExecutionHelpers.cases_at hZ1 w B n t (add hw A) (add hB A) (add ht A))
    · exact PacketVarintExecutionUniqueCases.small_cases (ZFContext.add hZ1 _) w B n s t (add (add hw A) _) (add (add hB A) _) (add hA _) (.hyp (Or.inl rfl))
    · exact .botE (PacketVarintExecutionUniqueValues.large_not_small (ZFContext.add hZ1 _) w B n t (add (add hw A) _) (add (.conjL hA) _) (.hyp (Or.inl rfl)))
  · let A := PacketVarintCanonicalRecursionSyntax.largeCase true w B n s
    have hZ1 := ZFContext.add hZ A
    have hA : Derives (Context.add A Γ) A := .hyp (Or.inl rfl)
    apply Derives.disjE (PacketVarintExecutionHelpers.cases_at hZ1 w B n t (add hw A) (add hB A) (add ht A))
    · exact .botE (PacketVarintExecutionUniqueValues.large_not_small (ZFContext.add hZ1 _) w B n s (add (add hw A) _) (.conjL (.hyp (Or.inl rfl))) (add hA _))
    · exact PacketVarintExecutionUniqueCases.large_cases (ZFContext.add hZ1 _) w B n s t (add (add hw A) _) (add (add hB A) _) (add (add hi A) _) (add hA _) (.hyp (Or.inl rfl))

theorem unique_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hi : Derives Γ (earlier w n)) : Derives Γ (unique w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let A := canonical (old 2 w : Fin (m+2)) (old 2 n) (slot 2 0)
  let B0 := canonical (old 2 w : Fin (m+2)) (old 2 n) (slot 2 1)
  let Δ := Context.add B0 (Context.add A (raisedContext 2 Γ))
  have hZ2 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) A) B0
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_many 2 hB)
  have hi2 := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_many 2 hi)
  exact point hZ2 (old 2 w) (old 2 B) (old 2 n) (slot 2 0) (slot 2 1) (add (add hw2 A) B0) (add (add hB2 A) B0) (add (add hi2 A) B0)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketVarintExecutionUnique
