import PPAC.Migration.Internal.PacketHornAffineLawSyntax

/-! Complete all-internal local rule laws; only omega is needed to construct their actual literal systems. -/
namespace PPAC.Migration.Internal.PacketHornAffineLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketHornAffineLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem base_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (baseLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := environmentNat 1 (old 3 w : Fin (m+3)) (fun _ => slot 3 0)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw H)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 3)) (HornBinderRules.under_body 3 hB H)
  exact PacketHornAffineLocal.base_iff (HornBinderRules.zf_body 3 hZ H) wide (old 3 w) (old 3 B)
    (slot 3 1) (slot 3 2) (fun _ => slot 3 0) hw3 (.hyp (Or.inl rfl)) hB3

theorem step_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (stepLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := environmentNat 3 (old 5 w : Fin (m+5)) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 1) (slot 5 2))
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw H)
  have hB5 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 5)) (HornBinderRules.under_body 5 hB H)
  exact PacketHornAffineLocal.step_iff (HornBinderRules.zf_body 5 hZ H) wide (old 5 w) (old 5 B)
    (slot 5 3) (slot 5 4) (SyntaxAtomSyntax.three (slot 5 0) (slot 5 1) (slot 5 2)) hw5 (.hyp (Or.inl rfl)) hB5

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let P := PacketAffineLiteralSyntax.frame wide w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hZ1 := ZFContext.under hZ P
  have hA := base_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP)
  have hS := step_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP)
  have hSys : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hP (.conjI hA hS)
  have ho : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hSys
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm ho

end PPAC.Migration.Internal.PacketHornAffineLaws
