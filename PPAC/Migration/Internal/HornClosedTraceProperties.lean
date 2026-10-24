import PPAC.Migration.Internal.HornClosedTraceSystemSyntax

/-! Uniform internal unfolding retains invalid root candidates and constructs its trace by Separation. -/
namespace PPAC.Migration.Internal.HornClosedTraceProperties
open Source SourceAlgebra SourceLogic OmegaSyntax HornClosedTraceValueSyntax HornClosedTraceSystemSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem step_natural {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w r V : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (HornStepSyntax.step rules w r V)) : Derives Γ (.mem r w) := by
  apply HornStepSyntax.step_elim rules w r V _ hs
  intro rule hr
  apply Derives.impI
  exact HornApplicationRange.range (ZFContext.add hZ _) rule w r V (add hw _) (.hyp (Or.inl rfl))

theorem reject_non_natural {m} {Γ : Context m} (rules : List Rule) (w r : Fin m)
    (hr : Derives Γ ((Formula.mem r w).neg)) : Derives Γ ((HornClosedTraceSyntax.condition rules w r).neg) := by
  apply Derives.impI
  exact .impE (add hr _) (HornClosedTraceValue.condition_natural rules w r (.hyp (Or.inl rfl)))

theorem unfold_iff {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value rules w V)) :
    Derives Γ ((HornClosedTraceSyntax.condition rules w r).iff (HornStepSyntax.step rules w r V)) := by
  apply Derives.conjI
  · exact .impI (HornClosedTraceValueClosed.condition_step rules w V r (add hv _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hs : Derives (Context.add (HornStepSyntax.step rules w r V) Γ) (HornStepSyntax.step rules w r V) := .hyp (Or.inl rfl)
    exact HornClosedTraceValueClosed.step_condition rules (ZFContext.add hZ _) w V r (add hv _)
      (step_natural rules (ZFContext.add hZ _) w r V (add hw _) hs) hs

theorem all_unfold {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value rules w V)) : Derives Γ (allLaw rules w V) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hv1 := of_eq (value_rename rules w V Fin.castSucc) (Derives.rename Fin.castSucc hv)
  exact unfold_iff rules (ZFContext.rename hZ Fin.castSucc) w.castSucc V.castSucc (Fin.last m) hw1 hv1

theorem exists_system {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem rules w) := by
  let P := value rules w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (HornClosedTraceValue.exists_value rules hZ w)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hC := HornClosedTraceValueClosed.closed rules w.castSucc (Fin.last m) hP
  have hA := all_unfold rules (ZFContext.under hZ P) w.castSucc (Fin.last m) hw1 hP
  have hSys : Derives Δ (system rules w.castSucc (Fin.last m)) := .conjI hP (.conjI hC hA)
  have ho : Derives Δ (existsSystem rules w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hSys
  exact of_eq (existsSystem_rename rules w Fin.castSucc).symm ho

end PPAC.Migration.Internal.HornClosedTraceProperties
