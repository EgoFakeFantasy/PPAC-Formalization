import PPAC.Migration.Internal.HornClosedTraceValueSyntax

/-! ZF内实际取得全部原轨迹根集合，并包含每个内部闭轨迹；不选择外部轨迹函数。 -/
namespace PPAC.Migration.Internal.HornClosedTraceValue
open Source SourceAlgebra SourceLogic HornClosedTraceValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem exists_value {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (existsValue rules w) := by
  have hh := MinimalInstances.separation_instance (HornClosedTraceValueSyntax.matrix rules) (one w) w (ZFContext.separation hZ (HornClosedTraceValueSyntax.matrix rules))
  have hm : ReplacementPredicates.paramsUp (one w) = one w.castSucc := rfl
  exact of_eq (by simp only [MinimalPredicates.separationExists, existsValue, value, hm]) hh

theorem subset {m} {Γ : Context m} (rules : List Rule) (w V : Fin m) (hv : Derives Γ (value rules w V)) : Derives Γ (RestrictionSyntax.subset V w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value rules w.castSucc V.castSucc) := of_eq (value_rename rules w V Fin.castSucc) (under hv M)
  exact .conjL (.impE (.conjL (value_at rules _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem condition_natural {m} {Γ : Context m} (rules : List Rule) (w r : Fin m)
    (hc : Derives Γ (HornClosedTraceSyntax.condition rules w r)) : Derives Γ (.mem r w) := by
  let B := HornClosedTraceSyntax.witness rules w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (RestrictionSyntax.subset_at _ _ _ (.conjL hB)) (.conjL (.conjR hB))

theorem member_iff {m} {Γ : Context m} (rules : List Rule) (w V r : Fin m) (hv : Derives Γ (value rules w V)) :
    Derives Γ ((Formula.mem r V).iff (HornClosedTraceSyntax.condition rules w r)) := by
  have he := value_at rules w V r hv
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hc : Derives (Context.add (HornClosedTraceSyntax.condition rules w r) Γ) (HornClosedTraceSyntax.condition rules w r) := .hyp (Or.inl rfl)
    exact .impE (add (.conjR he) _) (.conjI (condition_natural rules w r hc) hc)

theorem subtrace_included {m} {Γ : Context m} (rules : List Rule) (w V R : Fin m) (hv : Derives Γ (value rules w V))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (HornClosedTraceSyntax.closed rules w R)) :
    Derives Γ (RestrictionSyntax.subset R V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value rules w.castSucc V.castSucc) := of_eq (value_rename rules w V Fin.castSucc) (under hv M)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs M)
  have hc1 : Derives Δ (HornClosedTraceSyntax.closed rules w.castSucc R.castSucc) := of_eq (HornClosedTraceSyntax.closed_rename rules w R Fin.castSucc) (under hc M)
  have hm : Derives Δ M := .hyp (Or.inl rfl)
  have ht := HornClosedTraceSyntax.intro_condition rules w.castSucc (Fin.last m) R.castSucc (.conjI hs1 (.conjI hm hc1))
  exact .impE (.conjR (member_iff rules _ _ _ hv1)) ht

end PPAC.Migration.Internal.HornClosedTraceValue
