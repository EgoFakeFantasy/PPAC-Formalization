import PPAC.Migration.Internal.OriginalFullFormulaProgram

/-! 完整原运行/根执行的对象归纳步；实际历史在对象存在量词内取得，十一参数全部量化。 -/
namespace PPAC.Migration.Internal.OriginalFormulaCorrectnessPoint
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_at_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b a c n) :=
  .conjI hn (IndexTermImageCodeTyping.environment_lists w I J R S a b a c
    (OriginalOperationFrameRules.environment hZ three w mode depth P a b c I J R S hw hf))

theorem execution_iff_from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S h q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n)) (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformExecutionSyntax.executed w R S a b a c n q)) := by
  have hp := OriginalFullFormulaProgram.program_iff hZ three w n mode depth P a b c I J R S h q hw hi hf hn hg
  have he := FormulaTransformRootStep.execution_iff_program hZ w R S a b a c h n q hw
    (input_at_frame hZ three w n mode depth P a b c I J R S hw hf hn) hg
  exact iff_trans hp (.conjI (.conjR he) (.conjL he))

theorem execution_iff_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n)) (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformExecutionSyntax.executed w R S a b a c n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  let B := FormulaTransformRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 B _ (FormulaTransformRecursionCorrectness.graph_exists hZ w n hw ho)
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hi1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three (old 1 w) (old 1 n)) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n (old 1)) (HornBinderRules.under_body 1 hi B)
  have hf1 : Derives Δ (OriginalOperationFrameSyntax.frame three (old 1 w) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 I) (old 1 J) (old 1 R) (old 1 S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S (old 1)) (HornBinderRules.under_body 1 hf B)
  have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 a) (old 1 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 1)) (HornBinderRules.under_body 1 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := execution_iff_from_graph (HornBinderRules.zf_body 1 hZ B) three (old 1 w) (old 1 n) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 I) (old 1 J) (old 1 R) (old 1 S) (slot 1 0) (old 1 q) hw1 hi1 hf1 hn1 hB
  exact of_eq (by simp only [Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformExecutionSyntax.executed_rename, OriginalOperationFrameSyntax.parameter_map]) ht

theorem correct_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n)) :
    Derives Γ (OriginalUniformInductionSyntax.correct three w n) := by
  apply OriginalUniversalBlock.intro_many 11 (OriginalUniformInductionSyntax.body three w n)
  apply Derives.impI
  apply Derives.impI
  let F := OriginalOperationFrameSyntax.frame three (old 11 w) (slot 11 0) (slot 11 1) (slot 11 2) (slot 11 3) (slot 11 4) (slot 11 5) (slot 11 6) (slot 11 7) (slot 11 8) (slot 11 9)
  let C := FormulaCodeSyntax.formulaCode (old 11 w) (old 11 n) (slot 11 3) (slot 11 4)
  let Δ := Context.add C (Context.add F (raisedContext 11 Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 11 hZ) F) C
  have hw1 : Derives Δ (omega (old 11 w)) := add (add (of_eq (omega_rename w (old 11)) (HornBinderRules.under_many 11 hw)) F) C
  have hi1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three (old 11 w) (old 11 n)) := add (add (of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n (old 11)) (HornBinderRules.under_many 11 hi)) F) C
  have hf : Derives Δ F := .hyp (Or.inr (Or.inl rfl))
  have hn : Derives Δ C := .hyp (Or.inl rfl)
  exact execution_iff_from_induction hZ1 three (old 11 w) (old 11 n) (slot 11 0) (slot 11 1) (slot 11 2) (slot 11 3) (slot 11 4) (slot 11 5) (slot 11 6) (slot 11 7) (slot 11 8) (slot 11 9) (slot 11 10) hw1 hi1 hf hn

end PPAC.Migration.Internal.OriginalFormulaCorrectnessPoint
