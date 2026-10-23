import PPAC.Migration.Internal.HornLookupSome

/-! 原ObjectTrace幂集载体的纯对象展开：实际取得P(ω)，所有内部轨迹成员与子集精确对应。 -/
namespace PPAC.Migration.Internal.HornLookupPowerCondition
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def atPower {m} (w r P : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) P.castSucc).conj ((Formula.mem r.castSucc (Fin.last m)).conj (HornLookupSearchCondition.closed w.castSucc (Fin.last m))))

def condition {m} (w r : Fin m) : Formula m := .ex
  ((PowerSetSyntax.powerOf (Fin.last m) w.castSucc).conj (atPower w.castSucc r.castSucc (Fin.last m)))

theorem atPower_rename {m k} (w r P : Fin m) (ρ : Fin m → Fin k) :
    (atPower w r P).rename ρ = atPower (ρ w) (ρ r) (ρ P) := by
  simp only [atPower, Formula.rename, HornLookupSearchCondition.closed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem condition_rename {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, PowerSetSyntax.powerOf_rename, atPower_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_condition {m} {Γ : Context m} (w r P : Fin m) (hp : Derives Γ (PowerSetSyntax.powerOf P w))
    (hc : Derives Γ (atPower w r P)) : Derives Γ (condition w r) := by
  apply Derives.exI P
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PowerSetSyntax.powerOf_rename, atPower_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hp hc)

theorem at_power_iff {m} {Γ : Context m} (w r P : Fin m) (hp : Derives Γ (PowerSetSyntax.powerOf P w)) :
    Derives Γ ((atPower w r P).iff (HornLookupSearchCondition.condition w r)) := by
  apply FormulaCodeCongruence.ex_congr
  have hp1 := of_eq (PowerSetSyntax.powerOf_rename P w Fin.castSucc) (Derives.rename Fin.castSucc hp)
  exact FormulaCodeCongruence.conj_congr (PowerSetSyntax.power_at P.castSucc w.castSucc (Fin.last m) hp1)
    (SyntaxTypeLocalTransfer.iff_refl ((Formula.mem r.castSucc (Fin.last m)).conj (HornLookupSearchCondition.closed w.castSucc (Fin.last m))))

theorem search_condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) :
    Derives Γ ((condition w r).iff (HornLookupSearchCondition.condition w r)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := condition w r
    let B := (PowerSetSyntax.powerOf (Fin.last m) w.castSucc).conj (atPower w.castSucc r.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjL (at_power_iff _ _ _ (.conjL hB))) (.conjR hB)
    exact of_eq (HornLookupSearchCondition.condition_rename w r Fin.castSucc).symm ho
  · apply Derives.impI
    let E := HornLookupSearchCondition.condition w r
    have he := PowerSetSyntax.power_instance w (Derives.hyp ((ZFContext.add hZ E) _ ⟨_, Source.SetLanguage.IsZFAxiom.powerSet, rfl⟩))
    let B := PowerSetSyntax.powerOf (Fin.last m) w.castSucc
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hc : Derives Δ (HornLookupSearchCondition.condition w.castSucc r.castSucc) := of_eq (HornLookupSearchCondition.condition_rename w r Fin.castSucc)
      (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hp := Derives.impE (.conjR (at_power_iff _ _ _ hB)) hc
    have ho := intro_condition _ _ _ hB hp
    exact of_eq (condition_rename w r Fin.castSucc).symm ho

theorem execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) :
    Derives Γ ((condition w r).iff (LookupTableExecutionSyntax.executed w n i y)) :=
  SyntaxTypeLocalTransfer.iff_trans (search_condition_iff hZ w r) (HornLookupSearchCondition.execution_iff hZ w n i y r hw hr)

end PPAC.Migration.Internal.HornLookupPowerCondition
