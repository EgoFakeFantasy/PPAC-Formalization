import PPAC.Migration.Internal.HornLookupCondition

/-! 原实际S(row)有界搜索的任意内部轨迹，与原全表应用轨迹精确对应。 -/
namespace PPAC.Migration.Internal.HornLookupSearchCondition
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def closed {m} (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (HornSearchSyntax.originalSearchStep w.castSucc (Fin.last m) R.castSucc))

def witness {m} (w r R : Fin m) : Formula m :=
  (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed w R))

def condition {m} (w r : Fin m) : Formula m := .ex (witness w.castSucc r.castSucc (Fin.last m))

theorem closed_rename {m k} (w R : Fin m) (ρ : Fin m → Fin k) :
    (closed w R).rename ρ = closed (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, HornSearchSyntax.originalSearchStep_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m k} (w r R : Fin m) (ρ : Fin m → Fin k) :
    (witness w r R).rename ρ = witness (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, HornLookupSearchCondition.closed_rename]

theorem condition_rename {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_condition {m} {Γ : Context m} (w r R : Fin m) (hw : Derives Γ (witness w r R)) : Derives Γ (condition w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hw

theorem closed_at {m} {Γ : Context m} (w R r : Fin m) (hc : Derives Γ (closed w R)) (hm : Derives Γ (.mem r R)) :
    Derives Γ (HornSearchSyntax.originalSearchStep w r R) := by
  have hh : Derives Γ ((Formula.mem r R).imp (HornSearchSyntax.originalSearchStep w r R)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, HornSearchSyntax.originalSearchStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE hh hm

theorem closed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (RestrictionSyntax.subset R w)) :
    Derives Γ ((HornLookupSoundSyntax.closed w R).iff (closed w R)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.allI
    apply Derives.impI
    let C := HornLookupSoundSyntax.closed w R
    let M := Formula.mem (Fin.last m) R.castSucc
    let Δ := Context.add M (Context.image Formula.raise (Context.add C Γ))
    have hZ1 := ZFContext.under (ZFContext.add hZ C) M
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw C) M)
    have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under (add hs C) M)
    have hc1 : Derives Δ (HornLookupSoundSyntax.closed w.castSucc R.castSucc) := of_eq (HornLookupSoundSyntax.closed_rename w R Fin.castSucc)
      (under (Derives.hyp (Γ := Context.add C Γ) (Or.inl rfl)) M)
    have hm : Derives Δ M := .hyp (Or.inl rfl)
    have hr := Derives.impE (RestrictionSyntax.subset_at _ _ _ hs1) hm
    exact .impE (.conjL (HornSearchRules.step_iff_search hZ1 YesMetaZFC.Automation.ObjectSyntaxTransform.rules _ _ _ hw1 hr))
      (HornLookupSoundSyntax.closed_at _ _ _ hc1 hm)
  · apply Derives.impI
    apply Derives.allI
    apply Derives.impI
    let C := closed w R
    let M := Formula.mem (Fin.last m) R.castSucc
    let Δ := Context.add M (Context.image Formula.raise (Context.add C Γ))
    have hZ1 := ZFContext.under (ZFContext.add hZ C) M
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw C) M)
    have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under (add hs C) M)
    have hc1 : Derives Δ (closed w.castSucc R.castSucc) := of_eq (HornLookupSearchCondition.closed_rename w R Fin.castSucc)
      (under (Derives.hyp (Γ := Context.add C Γ) (Or.inl rfl)) M)
    have hm : Derives Δ M := .hyp (Or.inl rfl)
    have hr := Derives.impE (RestrictionSyntax.subset_at _ _ _ hs1) hm
    exact .impE (.conjR (HornSearchRules.step_iff_search hZ1 YesMetaZFC.Automation.ObjectSyntaxTransform.rules _ _ _ hw1 hr)) (closed_at _ _ _ hc1 hm)

theorem condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (condition w r)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornLookupConditionSyntax.condition w r
    let B := HornLookupConditionSyntax.witness w.castSucc r.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc := Derives.impE (.conjL (closed_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ hw1 (.conjL hB))) (.conjR (.conjR hB))
    have ho := intro_condition _ _ _ (.conjI (.conjL hB) (.conjI (.conjL (.conjR hB)) hc))
    exact of_eq (condition_rename w r Fin.castSucc).symm ho
  · apply Derives.impI
    let E := condition w r
    let B := witness w.castSucc r.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc := Derives.impE (.conjR (closed_iff (ZFContext.under (ZFContext.add hZ E) B) _ _ hw1 (.conjL hB))) (.conjR (.conjR hB))
    have ho := HornLookupConditionSyntax.intro_condition _ _ _ (.conjI (.conjL hB) (.conjI (.conjL (.conjR hB)) hc))
    exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ho

theorem execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) :
    Derives Γ ((condition w r).iff (LookupTableExecutionSyntax.executed w n i y)) := by
  have hh := condition_iff hZ w r hw
  exact SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hh) (.conjL hh)) (HornLookupCondition.execution_iff hZ w n i y r hw hr)

end PPAC.Migration.Internal.HornLookupSearchCondition
