import PPAC.Migration.Internal.OriginalAtomicRunDispatch
import PPAC.Migration.Internal.FormulaTransformValue
import PPAC.Migration.Internal.FormulaTransformStepCorrectness
import PPAC.Migration.Internal.SyntaxMixedFormulaCaseTyping

/-! 真实十一分支程序的目标类型与根执行方程；保留并实际推出合法性守卫，不要求原运行归纳前提。 -/
namespace PPAC.Migration.Internal.FormulaTransformRootStep
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)
open OriginalAtomicRunDispatch (disj_imp)

theorem recursive_target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  have hctx := SyntaxMixedFormulaCaseTyping.target_contexts w R S a b c d n hi
  have h0 : Derives Γ ((SyntaxMixedFormulaAtomSyntax.nullary false w a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.nullary (ZFContext.add hZ _) false w a b c d n q (add hw _) (.hyp (Or.inl rfl)))
  have h1 : Derives Γ ((SyntaxMixedFormulaAtomSyntax.nullary true w a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.nullary (ZFContext.add hZ _) true w a b c d n q (add hw _) (.hyp (Or.inl rfl)))
  have h2 : Derives Γ ((SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.membership (ZFContext.add hZ _) w R S a b c d n q (add hw _) (.hyp (Or.inl rfl)))
  have h3 : Derives Γ ((SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.equality (ZFContext.add hZ _) w R S a b c d n q (add hw _) (.hyp (Or.inl rfl)))
  have h4 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.single 4 false w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.single (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl, rfl⟩) w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h5 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.binary 0 w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.binary (ZFContext.add hZ _) 0 w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h6 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.binary 1 w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.binary (ZFContext.add hZ _) 1 w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h7 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.binary 2 w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.binary (ZFContext.add hZ _) 2 w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h8 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.binary 3 w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.binary (ZFContext.add hZ _) 3 w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h9 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.single 9 true w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.single (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  have h10 : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.single 10 true w R S a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)) :=
    .impI (SyntaxMixedFormulaCaseTyping.single (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S a b c d n q (add hw _) (add hctx _) (.hyp (Or.inl rfl)))
  exact .impE (disj_imp (disj_imp h0 h1) (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 (disj_imp h7 (disj_imp h8 (disj_imp h9 h10))))))))) hc

theorem program_target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hp : Derives Γ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  have hn := Derives.conjL (FormulaCodeProperties.guards w n a b (.conjL hi))
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have localCases := Derives.impE (.conjL (FormulaTransformStepCorrectness.program_iff hZ w R S a b c d h n q hw)) hp
  have recursiveCases := Derives.impE (.conjL (SyntaxMixedFormulaLocalTransfer.all_iff hZ w R S a b c d h n q ho oldGraph)) localCases
  exact recursive_target_type hZ w R S a b c d n q hw hi recursiveCases

theorem execution_iff_guarded_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w)) (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff
      ((Formula.mem n w).conj ((SyntaxMixedFormulaStateSyntax.legal w R S a b c d q).conj
        (FormulaTransformProgramSyntax.step w R S a b c d h n q)))) := by
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have hs := iff_trans (FormulaTransformStepCorrectness.step_iff hZ w R S a b c d h n q hw)
    (SyntaxMixedFormulaLocalTransfer.content_iff hZ w R S a b c d h n q ho oldGraph)
  exact iff_trans (FormulaTransformRecursionCorrectness.execution_iff hZ w R S a b c d n q hw)
    (iff_trans (SyntaxMixedFormulaRecursive.recursive_iff hZ w R S a b c d n q hw)
      (conj_congr (iff_refl _) (conj_congr (iff_refl _) (.conjI (.conjR hs) (.conjL hs)))))

theorem execution_iff_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff
      (FormulaTransformProgramSyntax.step w R S a b c d h n q)) := by
  have hn := Derives.conjL (FormulaCodeProperties.guards w n a b (.conjL hi))
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have he := execution_iff_guarded_step hZ w R S a b c d h n q hw ho hg
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    have hstep : Derives (Context.add (FormulaTransformProgramSyntax.step w R S a b c d h n q) Γ)
        (FormulaTransformProgramSyntax.step w R S a b c d h n q) := .hyp (Or.inl rfl)
    have hq := program_target_type (ZFContext.add hZ _) w R S a b c d h n q (add hw _) (add hi _) (add hg _) (.conjR hstep)
    have hl : Derives (Context.add (FormulaTransformProgramSyntax.step w R S a b c d h n q) Γ)
        (SyntaxMixedFormulaStateSyntax.legal w R S a b c d q) := .conjI (add (.conjR hi) _) hq
    exact .impE (add (.conjR he) _) (.conjI (add hn _) (.conjI hl hstep))

theorem execution_iff_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)) := by
  have he := execution_iff_step hZ w R S a b c d h n q hw hi hg
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.conjI (add (.conjL hi) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.FormulaTransformRootStep
