import PPAC.Migration.Internal.PacketAffineApplicationLawSyntax

/-! All rows and trace candidates are object quantified; the radix witness is object eliminated. -/
namespace PPAC.Migration.Internal.PacketAffineApplicationLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineApplicationLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_many 2 hB)
  have hZ2 := HornBinderRules.zf_many 2 hZ
  exact .conjI (PacketAffineApplication.base_iff hZ2 wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) hw2 hB2)
    (PacketAffineApplication.step_iff hZ2 wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) hw2 hB2)

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let P := PacketAffineLiteralSyntax.frame wide w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hA := all_law (ZFContext.under hZ P) wide w.castSucc (Fin.last m) hw1 (.conjR hP)
  have hSys : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hP hA
  have ho : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hSys
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm ho

end PPAC.Migration.Internal.PacketAffineApplicationLaws
