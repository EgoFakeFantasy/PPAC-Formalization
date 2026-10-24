import PPAC.Migration.Internal.AbstractFullFormulaProgram

/-! mode1完整归纳步：真实历史EX取得／消去，十个变化参数全部内部全称绑定。 -/
namespace PPAC.Migration.Internal.AbstractFormulaCorrectnessPoint
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_at_frame {m} {Γ : Context m} (w n mode depth P a b c e R S : Fin m)
    (hf : Derives Γ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c e n) :=
  .conjI hn (AbstractOperationFrameSyntax.term_lists w mode depth P a b c e R S hf)

theorem execution_iff_from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S h q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n)) (hf : Derives Γ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformExecutionSyntax.executed w R S a b c e n q)) := by
  have hp := AbstractFullFormulaProgram.program_iff hZ w n mode depth P a b c e R S h q hw hi hf hn hg
  have he := FormulaTransformRootStep.execution_iff_program hZ w R S a b c e h n q hw
    (input_at_frame w n mode depth P a b c e R S hf hn) hg
  exact iff_trans hp (.conjI (.conjR he) (.conjL he))

theorem execution_iff_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n)) (hf : Derives Γ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformExecutionSyntax.executed w R S a b c e n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  let B := FormulaTransformRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 B _ (FormulaTransformRecursionCorrectness.graph_exists hZ w n hw ho)
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hi1 : Derives Δ (AbstractUniformInductionSyntax.allFramesIH (old 1 w) (old 1 n)) := of_eq (AbstractUniformInductionSyntax.allFramesIH_rename w n (old 1)) (HornBinderRules.under_body 1 hi B)
  have hf1 : Derives Δ (AbstractOperationFrameSyntax.frame (old 1 w) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S)) := of_eq (AbstractOperationFrameSyntax.frame_rename w mode depth P a b c e R S (old 1)) (HornBinderRules.under_body 1 hf B)
  have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 a) (old 1 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 1)) (HornBinderRules.under_body 1 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := execution_iff_from_graph (HornBinderRules.zf_body 1 hZ B) (old 1 w) (old 1 n) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S) (slot 1 0) (old 1 q) hw1 hi1 hf1 hn1 hB
  exact of_eq (by simp only [Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformExecutionSyntax.executed_rename]) ht

theorem correct_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n)) :
    Derives Γ (AbstractUniformInductionSyntax.correct w n) := by
  apply OriginalUniversalBlock.intro_many 10 (AbstractUniformInductionSyntax.body w n)
  apply Derives.impI
  apply Derives.impI
  let F := AbstractOperationFrameSyntax.frame (old 10 w) (slot 10 0) (slot 10 1) (slot 10 2) (slot 10 3) (slot 10 4) (slot 10 5) (slot 10 6) (slot 10 7) (slot 10 8)
  let C := FormulaCodeSyntax.formulaCode (old 10 w) (old 10 n) (slot 10 3) (slot 10 4)
  let Δ := Context.add C (Context.add F (raisedContext 10 Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 10 hZ) F) C
  have hw1 : Derives Δ (omega (old 10 w)) := add (add (of_eq (omega_rename w (old 10)) (HornBinderRules.under_many 10 hw)) F) C
  have hi1 : Derives Δ (AbstractUniformInductionSyntax.allFramesIH (old 10 w) (old 10 n)) := add (add (of_eq (AbstractUniformInductionSyntax.allFramesIH_rename w n (old 10)) (HornBinderRules.under_many 10 hi)) F) C
  have hf : Derives Δ F := .hyp (Or.inr (Or.inl rfl))
  have hn : Derives Δ C := .hyp (Or.inl rfl)
  exact execution_iff_from_induction hZ1 (old 10 w) (old 10 n) (slot 10 0) (slot 10 1) (slot 10 2) (slot 10 3) (slot 10 4) (slot 10 5) (slot 10 6) (slot 10 7) (slot 10 8) (slot 10 9) hw1 hi1 hf hn

end PPAC.Migration.Internal.AbstractFormulaCorrectnessPoint
