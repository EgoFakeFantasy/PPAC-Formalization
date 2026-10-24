import PPAC.Migration.Internal.ProjectionTraceSet

/-! 全部原投影轨迹根的实际集合仍对原七规则表闭合，并给出无外部有限性前提的原一步展开。 -/
namespace PPAC.Migration.Internal.ProjectionTraceUnfold
open Source SourceAlgebra SourceLogic ProjectionTraceSetSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem condition_step {m} {Γ : Context m} (w V r : Fin m) (hv : Derives Γ (value w V))
    (ht : Derives Γ (ProjectionTraceSyntax.condition w r)) : Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r V) := by
  let B := ProjectionTraceSyntax.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hv1 : Derives Δ (value w.castSucc V.castSucc) := of_eq (value_rename w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := ProjectionTraceSet.subtrace_included _ _ _ hv1 (.conjL hB) (.conjR (.conjR hB))
  have hs := ProjectionTraceSyntax.closed_at _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  exact of_eq (HornStepSyntax.step_rename YesMetaZFC.Automation.ObjectProjection.rules w r V Fin.castSucc).symm (HornTraceMonotone.step YesMetaZFC.Automation.ObjectProjection.rules _ _ _ _ hi hs)

theorem closed {m} {Γ : Context m} (w V : Fin m) (hv : Derives Γ (value w V)) : Derives Γ (ProjectionTraceSyntax.closed w V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value w.castSucc V.castSucc) := of_eq (value_rename w V Fin.castSucc) (under hv M)
  exact condition_step _ _ _ hv1 (.impE (.conjL (ProjectionTraceSet.member_iff _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem step_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value w V)) (hn : Derives Γ (.mem r w))
    (hs : Derives Γ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r V)) : Derives Γ (ProjectionTraceSyntax.condition w r) :=
  ProjectionTraceExtension.condition hZ w V r (ProjectionTraceSet.subset w V hv) hn (closed w V hv) hs

theorem unfold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value w V)) (hn : Derives Γ (.mem r w)) :
    Derives Γ ((ProjectionTraceSyntax.condition w r).iff (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r V)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact condition_step w V r (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact step_condition (ZFContext.add hZ _) w V r (add hv _) (add hn _) (.hyp (Or.inl rfl))

def unfolded {m} (w V : Fin m) : Formula m := (value w V).conj (.all
  ((Formula.mem (Fin.last m) w.castSucc).imp
    ((ProjectionTraceSyntax.condition w.castSucc (Fin.last m)).iff
      (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w.castSucc (Fin.last m) V.castSucc))))

def existsUnfolded {m} (w : Fin m) : Formula m := .ex (unfolded w.castSucc (Fin.last m))

theorem unfolded_rename {m k} (w V : Fin m) (ρ : Fin m → Fin k) :
    (unfolded w V).rename ρ = unfolded (ρ w) (ρ V) := by
  simp only [unfolded, Formula.iff, Formula.rename, value_rename, ProjectionTraceSyntax.condition_rename,
    HornStepSyntax.step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsUnfolded_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (existsUnfolded w).rename ρ = existsUnfolded (ρ w) := by
  simp only [existsUnfolded, Formula.rename, unfolded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actual_unfolded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V : Fin m)
    (hv : Derives Γ (value w V)) : Derives Γ (unfolded w V) := by
  apply Derives.conjI hv
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value w.castSucc V.castSucc) := of_eq (value_rename w V Fin.castSucc) (under hv M)
  exact unfold_iff (ZFContext.under hZ M) _ _ _ hv1 (.hyp (Or.inl rfl))

theorem exists_unfolded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) :
    Derives Γ (existsUnfolded w) := by
  let B := value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ProjectionTraceSet.exists_value hZ w)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsUnfolded w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, unfolded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (actual_unfolded (ZFContext.under hZ B) _ _ hB)
  exact of_eq (existsUnfolded_rename w Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectionTraceUnfold
