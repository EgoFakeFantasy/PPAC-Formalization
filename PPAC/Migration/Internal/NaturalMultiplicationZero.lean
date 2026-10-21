import PPAC.Migration.Internal.NaturalMultiplicationLaws

/-! 用对象ω归纳证明0×n=0，覆盖全部内部自然数而非外部逐例计算。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationZero
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalMultiplicationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def matrix : Formula 3 := product 0 1 2 1

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = product (ρ 0) (ρ 1) x (ρ 1) := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, product_rename, h0, h1, h2]

theorem base {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (OmegaInductionSyntax.base matrix (Source.SetLanguage.args2 w z)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := ArithmeticContext.rename hA Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hMul' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hMul
  have hw' : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hz' : Derives Δ (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have hzW := OmegaStructureAlgebra.zero_member w.castSucc z.castSucc hA'.base.extensionality hw' hz'
  apply Derives.impI
  have hx : Derives (Context.add (empty (Fin.last m)) Δ) (empty (Fin.last m)) := .hyp (Or.inl rfl)
  exact NaturalMultiplicationLaws.zero_backward (ArithmeticContext.add hA' _) w.castSucc z.castSucc (Fin.last m) z.castSucc
    (add hc' _) (add hMul' _) (add hw' _) (add hzW _) hx (add hz' _)

theorem step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (OmegaInductionSyntax.step matrix (Source.SetLanguage.args2 w z) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hMul' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hMul)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hz' : Derives Δ (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz)
  have hzW := OmegaStructureAlgebra.zero_member w.castSucc.castSucc z.castSucc.castSucc hA'.base.extensionality hw' hz'
  have hzsum := NaturalAdditionLaws.zero_value hA' w.castSucc.castSucc z.castSucc.castSucc z.castSucc.castSucc hc' hw' hzW hz'
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationLaws.successor_backward (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _)
    w.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) z.castSucc.castSucc z.castSucc.castSucc
    (add (add (add hc' _) _) _) (add (add (add hMul' _) _) _) (add (add (add hw' _) _) _) (add (add (add hzW _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl))) (add (add (add hzsum _) _) _)

theorem all_left_zero {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (product w.castSucc z.castSucc (Fin.last m) z.castSucc))) := by
  have hi := OmegaInduction.induction_on_omega matrix (Source.SetLanguage.args2 w z) w hs hw (base hA w z hc hMul hw hz) (step hA w z hc hMul hw hz)
  simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second] using hi
end PPAC.Migration.Internal.NaturalMultiplicationZero
