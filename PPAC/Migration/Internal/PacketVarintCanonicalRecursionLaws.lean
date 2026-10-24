import PPAC.Migration.Internal.PacketVarintCanonicalRecursionBridge

/-! Every internal canonical candidate has the exact independent terminal/continuation recursion with only omega. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalRecursionLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax PacketVarintCanonicalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (canonical w n s)) : Derives Γ (criterion w n s) := by
  let R := (SyntaxNumeralSyntax.numeral 128 (Fin.last m)).conj (canonicalAt w.castSucc (Fin.last m) n.castSucc s.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ht := Derives.impE (.conjL (PacketVarintCanonicalRecursionBridge.at_actual_iff hZ1 w.castSucc (Fin.last m) n.castSucc s.castSucc hw1 (.conjL hR))) (.conjR hR)
  simpa only [Formula.raise,criterion_rename] using intro_criterion w.castSucc (Fin.last m) n.castSucc s.castSucc (.conjL hR) ht

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (criterion w n s)) : Derives Γ (canonical w n s) := by
  let R := actualBody w n s
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ht := Derives.impE (.conjR (PacketVarintCanonicalRecursionBridge.at_actual_iff hZ1 w.castSucc (Fin.last m) n.castSucc s.castSucc hw1 (.conjL hR))) (.conjR hR)
  simpa only [Formula.raise,canonical_rename] using intro_actual w.castSucc (Fin.last m) n.castSucc s.castSucc (.conjL hR) ht

theorem actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((canonical w n s).iff (criterion w n s)) :=
  .conjI (.impI (forward (ZFContext.add hZ _) w n s (add hw _) (.hyp (Or.inl rfl))))
    (.impI (backward (ZFContext.add hZ _) w n s (add hw _) (.hyp (Or.inl rfl))))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  exact actual_iff (HornBinderRules.zf_many 2 hZ) (old 2 w) (slot 2 0) (slot 2 1) hw2

end PPAC.Migration.Internal.PacketVarintCanonicalRecursionLaws
