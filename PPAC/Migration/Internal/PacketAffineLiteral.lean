import PPAC.Migration.Internal.PacketAffineLiteralSyntax

/-! Actual 128/256 radix witnesses and their ALL-input affine laws are obtained inside original ZF. -/
namespace PPAC.Migration.Internal.PacketAffineLiteral
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineSyntax PacketAffineLiteralSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_fibers {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) : Derives Γ (totalLaw w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := (Formula.mem (slot 2 0 : Fin (m+2)) (old 2 B)).conj (.mem (slot 2 1) (old 2 w))
  let Δ := Context.add H (raisedContext 2 Γ)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := HornBinderRules.under_body 2 hB H
  exact PacketAffineFiber.exists_fiber (HornBinderRules.zf_body 2 hZ H) (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) hw2 hB2 (.conjL hH) (.conjR hH)

theorem frame_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B C : Fin m)
    (hB : Derives Γ (frame wide w B)) (hC : Derives Γ (frame wide w C)) : Derives Γ (.equal B C) :=
  SyntaxNumerals.unique hZ (PacketAffineRuleData.radix wide) B C (.conjR hB) (.conjR hC)

theorem zero_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B z : Fin m)
    (hB : Derives Γ (frame wide w B)) (hz : Derives Γ (empty z)) : Derives Γ (.mem z B) :=
  SyntaxNumerals.less hZ 0 (PacketAffineRuleData.radix wide) (by cases wide <;> decide) z B hz (.conjR hB)

theorem one_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B e : Fin m)
    (hB : Derives Γ (frame wide w B)) (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e)) : Derives Γ (.mem e B) :=
  SyntaxNumerals.less hZ 1 (PacketAffineRuleData.radix wide) (by cases wide <;> decide) e B he (.conjR hB)

theorem two_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B e : Fin m)
    (hB : Derives Γ (frame wide w B)) (he : Derives Γ (SyntaxNumeralSyntax.numeral 2 e)) : Derives Γ (.mem e B) :=
  SyntaxNumerals.less hZ 2 (PacketAffineRuleData.radix wide) (by cases wide <;> decide) e B he (.conjR hB)

theorem narrow_below_wide {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hB : Derives Γ (frame false w B)) (hC : Derives Γ (frame true w C)) : Derives Γ (.mem B C) :=
  SyntaxNumerals.less hZ 128 256 (by decide) B C (.conjR hB) (.conjR hC)

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let F := frame wide w.castSucc (Fin.last m)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have hT := all_fibers (ZFContext.under hZ F) w.castSucc (Fin.last m) hw1 (.conjL hF)
  have hR := PacketAffineRecursive.all_law (ZFContext.under hZ F) w.castSucc (Fin.last m) hw1 (.conjL hF)
  have hS : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hF (.conjI hT hR)
  have ho : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      hS
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm ho

end PPAC.Migration.Internal.PacketAffineLiteral
