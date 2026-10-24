import PPAC.Migration.Internal.ProofTreeTracedStep

/-! 原12规则的全内部闭轨迹递归方程；规范Separation集合在对象EX中构造并消去。 -/
namespace PPAC.Migration.Internal.ProofTreeTraceEquation
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def equation {m} (test : Formula 1) (w r : Fin m) : Formula m :=
  (Formula.mem r w).conj ((ProofTreeTracedStep.step test YesMetaZFC.Automation.ObjectProofTree.rules w r).conj
    (ProofTreeRowLocalSyntax.localCondition test w r))

theorem equation_rename {m l} (test : Formula 1) (w r : Fin m) (ρ : Fin m → Fin l) :
    (equation test w r).rename ρ = equation test (ρ w) (ρ r) := by
  simp only [equation, Formula.rename, ProofTreeTracedStep.step_rename, ProofTreeRowLocalSyntax.localCondition_rename]

theorem at_value_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((ProofTreeTraceSyntax.condition test w r).iff (equation test w r)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProofTreeTraceSyntax.condition test w r
    have he : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hs := ProofTreeUniversalClosed.condition_step test w V r (add hv E) he
    have ht := Derives.impE (.conjL (ProofTreeTracedStep.step_iff test _ w V r (add hv E))) (.conjL hs)
    exact .conjI (ProofTreeUniversalValue.condition_natural test w r he) (.conjI ht (.conjR hs))
  · apply Derives.impI
    let E := equation test w r
    have he : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hs := Derives.impE (.conjR (ProofTreeTracedStep.step_iff test _ w V r (add hv E))) (.conjL (.conjR he))
    exact ProofTreeUniversalClosed.step_condition test (ZFContext.add hZ E) w V r (add hv E) (.conjL he) (.conjI hs (.conjR (.conjR he)))

theorem recursive_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w r : Fin m) :
    Derives Γ ((ProofTreeTraceSyntax.condition test w r).iff (equation test w r)) := by
  let B := ProofTreeUniversalSyntax.value test w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ProofTreeUniversalValue.exists_value test hZ w)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_value_iff test (ZFContext.under hZ B) w.castSucc (Fin.last m) r.castSucc hB
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, ProofTreeTraceSyntax.condition_rename, equation_rename]) ho

end PPAC.Migration.Internal.ProofTreeTraceEquation
