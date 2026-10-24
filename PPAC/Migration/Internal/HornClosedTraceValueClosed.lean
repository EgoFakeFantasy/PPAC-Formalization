import PPAC.Migration.Internal.HornClosedTraceValue

/-! 全部原轨迹根的实际集合仍对原完整表闭合，并给出无外部有限性前提的原一步展开。 -/
namespace PPAC.Migration.Internal.HornClosedTraceValueClosed
open Source SourceAlgebra SourceLogic HornClosedTraceValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem condition_step {m} {Γ : Context m} (rules : List Rule) (w V r : Fin m) (hv : Derives Γ (value rules w V))
    (ht : Derives Γ (HornClosedTraceSyntax.condition rules w r)) : Derives Γ (HornStepSyntax.step rules w r V) := by
  let B := HornClosedTraceSyntax.witness rules w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hv1 : Derives Δ (value rules w.castSucc V.castSucc) := of_eq (value_rename rules w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornClosedTraceValue.subtrace_included rules _ _ _ hv1 (.conjL hB) (.conjR (.conjR hB))
  have hs := HornClosedTraceSyntax.closed_at rules _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  exact of_eq (HornStepSyntax.step_rename rules w r V Fin.castSucc).symm (HornTraceMonotone.step rules _ _ _ _ hi hs)

theorem closed {m} {Γ : Context m} (rules : List Rule) (w V : Fin m) (hv : Derives Γ (value rules w V)) : Derives Γ (HornClosedTraceSyntax.closed rules w V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value rules w.castSucc V.castSucc) := of_eq (value_rename rules w V Fin.castSucc) (under hv M)
  exact condition_step rules _ _ _ hv1 (.impE (.conjL (HornClosedTraceValue.member_iff rules _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem step_condition {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value rules w V)) (hn : Derives Γ (.mem r w))
    (hs : Derives Γ (HornStepSyntax.step rules w r V)) : Derives Γ (HornClosedTraceSyntax.condition rules w r) :=
  HornClosedTraceExtension.condition rules hZ w V r (HornClosedTraceValue.subset rules w V hv) hn (closed rules w V hv) hs

theorem unfold_iff {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value rules w V)) (hn : Derives Γ (.mem r w)) :
    Derives Γ ((HornClosedTraceSyntax.condition rules w r).iff (HornStepSyntax.step rules w r V)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact condition_step rules w V r (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact step_condition rules (ZFContext.add hZ _) w V r (add hv _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornClosedTraceValueClosed
