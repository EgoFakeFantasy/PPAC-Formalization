import PPAC.Migration.Internal.StructuralListProjection

/-! 原Cons投影的总单值前提已消去；实际内部递归图、全自然索引唯一值和逐步方程。 -/
namespace PPAC.Migration.Internal.StructuralListProjectionRecursion
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax ReplacementPredicates
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem total {m} {Γ : Context m} (head : Bool) (ρ : Fin 1 → Fin m) (hw : Derives Γ (omega (ρ 0))) :
    Derives Γ (NaturalRecursionSyntax.relationTotal (matrix head) ρ) := by
  simp only [NaturalRecursionSyntax.relationTotal, matrix_rel, paramsUp]
  apply Derives.allI
  have hw1 : Derives (Context.image Formula.raise Γ) (omega (ρ 0).castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  exact StructuralListProjection.exists_step head (ρ 0).castSucc (Fin.last m) hw1

theorem functional {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (NaturalRecursionSyntax.relationFunctional (matrix head) ρ) := by
  simp only [NaturalRecursionSyntax.relationFunctional, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hw3 : Derives Δ (omega (ρ 0).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrdinalRestriction.raise_three hw
  apply Derives.impI
  apply Derives.impI
  exact StructuralListProjection.functional_point (ZFContext.add (ZFContext.add hZ3 _) _) head _ _ _ _
    (add (add hw3 _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (NaturalEvaluationRange.range (matrix head) ρ (ρ 0)) := by
  simp only [NaturalEvaluationRange.range, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  exact StructuralListProjection.range_point (ZFContext.add hZ2 _) head _ _ _ (add hw2 _) (.hyp (Or.inl rfl))

theorem actual_recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (recursors head w a) := by
  have hc := ZFContext.closed hZ (NaturalRecursion.source_uniqueness (matrix head))
  exact ObjectNaturalRecursion.instantiate_unique (matrix head) (params w) w a hc hw
    (total head (params w) hw) (functional hZ head (params w) hw)

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) : Derives Γ (iterationFiber head w a r) := by
  have hA := ZFContext.arithmetic hZ
  exact NaturalEvaluationFiber.at_natural (matrix head) (params w) w a r hA.base.extensionality hw hr
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw) (actual_recursors hZ head w a hw)

theorem iteration_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hy : Derives Γ (iteration head w a r y)) : Derives Γ (.mem y w) :=
  NaturalEvaluationRange.evaluation_range (matrix head) (params w) w a r y w ha (range hZ head (params w) hw) hy

theorem iteration_zero {m} {Γ : Context m} (head : Bool) (w a r y : Fin m)
    (hr : Derives Γ (empty r)) (hy : Derives Γ (iteration head w a r y)) : Derives Γ (.equal y a) :=
  NaturalRecursionLaws.evaluation_zero (matrix head) (params w) w a r y hr hy

theorem iteration_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r s u v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hu : Derives Γ (iteration head w a r u)) (hv : Derives Γ (iteration head w a s v)) : Derives Γ (step head w u v) := by
  have hA := ZFContext.arithmetic hZ
  simpa only [matrix_rel, params] using NaturalEvaluationStep.evaluation_step hA (matrix head) (params w) w a r s u v hw hr hs
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw) (actual_recursors hZ head w a hw) hu hv
end PPAC.Migration.Internal.StructuralListProjectionRecursion
