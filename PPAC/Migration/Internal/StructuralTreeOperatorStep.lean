import PPAC.Migration.Internal.StructuralTreeOperatorLogic

/-! 具体树前段二值算子的实际总单值性、真实0/1范围与局部求值。 -/
namespace PPAC.Migration.Internal.StructuralTreeOperatorStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_step {m} {Γ : Context m} (w z e n h : Fin m) : Derives Γ (.ex (step w.castSucc z.castSucc e.castSucc n.castSucc h.castSucc (Fin.last m))) := by
  apply SourcePropositional.by_cases (good w e n h) _
  · apply Derives.exI e
    simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .disjL (.conjI (.hyp (Or.inl rfl)) (.eqRefl e))
  · apply Derives.exI z
    simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .disjR (.conjI (.hyp (Or.inl rfl)) (.eqRefl z))

theorem functional_point {m} {Γ : Context m} (w z e n h y u : Fin m)
    (hy : Derives Γ (step w z e n h y)) (hu : Derives Γ (step w z e n h u)) : Derives Γ (.equal y u) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hu _)
    · exact eq_trans (.conjR (.hyp (Or.inr (Or.inl rfl)))) (eq_symm (.conjR (.hyp (Or.inl rfl))))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hu _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (.conjL (.hyp (Or.inl rfl))))
    · exact eq_trans (.conjR (.hyp (Or.inr (Or.inl rfl)))) (eq_symm (.conjR (.hyp (Or.inl rfl))))

theorem on_good {m} {Γ : Context m} (w z e n h y : Fin m) (hg : Derives Γ (good w e n h))
    (hy : Derives Γ (step w z e n h y)) : Derives Γ (.equal y e) := by
  apply Derives.disjE hy
  · exact .conjR (.hyp (Or.inl rfl))
  · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hg _))

theorem off_good {m} {Γ : Context m} (w z e n h y : Fin m) (hg : Derives Γ (good w e n h).neg)
    (hy : Derives Γ (step w z e n h y)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · exact .botE (.impE (add hg _) (.conjL (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

theorem on_zero {m} {Γ : Context m} (w z e n h y : Fin m) (hz : Derives Γ (empty n))
    (hy : Derives Γ (step w z e n h y)) : Derives Γ (.equal y z) :=
  off_good w z e n h y (StructuralTreeOperatorLogic.empty_not_good w e n h hz) hy

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n h y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hy : Derives Γ (step w z e n h y)) : Derives Γ ((Formula.mem y w).conj ((Formula.equal y z).disj (.equal y e))) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := StructuralListUnits.member hZ w z e hw hz he
  apply Derives.disjE hy
  · have hEq : Derives (Context.add ((good w e n h).conj (.equal y e)) Γ) (.equal y e) := .conjR (.hyp (Or.inl rfl))
    exact .conjI (mem_subst (eq_symm hEq) (add heW _)) (.disjR hEq)
  · have hEq : Derives (Context.add ((good w e n h).neg.conj (.equal y z)) Γ) (.equal y z) := .conjR (.hyp (Or.inl rfl))
    exact .conjI (mem_subst (eq_symm hEq) (add hzW _)) (.disjL hEq)

theorem total {m} {Γ : Context m} (ρ : Fin 3 → Fin m) : Derives Γ (OrdinalRecursionTotal.total matrix ρ) := by
  simp only [OrdinalRecursionTotal.total, OrdinalRecursionTotal.hasValue, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  exact exists_step _ _ _ _ _

theorem deterministic {m} {Γ : Context m} (ρ : Fin 3 → Fin m) : Derives Γ (OrdinalRecursionDeterminism.deterministic matrix ρ) := by
  simp only [OrdinalRecursionDeterminism.deterministic, OrdinalRecursionDeterminism.functional, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  exact functional_point _ _ _ _ _ _ _ (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralTreeOperatorStep
