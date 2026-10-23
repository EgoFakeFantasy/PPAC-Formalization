import PPAC.Migration.Internal.HornUniversalTraceValue

/-! 全部原轨迹根的实际集合仍对原完整表闭合，并给出无外部有限性前提的原一步展开。 -/
namespace PPAC.Migration.Internal.HornUniversalTraceClosed
open Source SourceAlgebra SourceLogic HornUniversalTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem condition_step {m} {Γ : Context m} (w V r : Fin m) (hv : Derives Γ (value w V))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (HornStepSyntax.originalStep w r V) := by
  let B := HornLookupConditionSyntax.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hv1 : Derives Δ (value w.castSucc V.castSucc) := of_eq (value_rename w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := HornUniversalTraceValue.subtrace_included _ _ _ hv1 (.conjL hB) (.conjR (.conjR hB))
  have hs := HornLookupSoundSyntax.closed_at _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  exact of_eq (HornStepSyntax.originalStep_rename w r V Fin.castSucc).symm (HornTraceMonotone.originalStep _ _ _ _ hi hs)

theorem closed {m} {Γ : Context m} (w V : Fin m) (hv : Derives Γ (value w V)) : Derives Γ (HornLookupSoundSyntax.closed w V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value w.castSucc V.castSucc) := of_eq (value_rename w V Fin.castSucc) (under hv M)
  exact condition_step _ _ _ hv1 (.impE (.conjL (HornUniversalTraceValue.member_iff _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem step_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value w V)) (hn : Derives Γ (.mem r w))
    (hs : Derives Γ (HornStepSyntax.originalStep w r V)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  HornTraceExtension.condition hZ w V r (HornUniversalTraceValue.subset w V hv) hn (closed w V hv) hs

theorem unfold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value w V)) (hn : Derives Γ (.mem r w)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (HornStepSyntax.originalStep w r V)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact condition_step w V r (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact step_condition (ZFContext.add hZ _) w V r (add hv _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornUniversalTraceClosed
