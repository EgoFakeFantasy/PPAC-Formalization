import PPAC.Migration.Internal.FormulaTransformBranchSelection
import PPAC.Migration.Internal.InstantiateBinderProgram
import PPAC.Migration.Internal.SmallModeLogicalFromInduction

/-! 在全参数对象归纳前提下，实际mode2全部十一种源公式情况对应同一真实完整程序。 -/
namespace PPAC.Migration.Internal.InstantiateFullFormulaProgram
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open OriginalAtomicRunDispatch (disj_imp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem atomic_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  exact iff_trans (InstantiateFrameAtomic.program_iff hZ w mode depth P a b c e R S h n q hw hf ha)
    (FormulaTransformBranchSelection.atomic_program_iff hZ w R S a b c e h n q hw ho hg ha)

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (x : Fin m)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  have hp := InstantiateUniformInductionRules.prefix_at_frame w n mode depth P a b c e R S hi hf
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have hb := iff_trans (FormulaTransformStepCorrectness.single_iff 4 false w h R S a b c e n q) (SyntaxMixedFormulaCaseTransfer.single_iff hZ 4 false w h R S a b c e n q ho oldGraph)
  have hr := SmallModeLogicalFromInduction.negation_iff hZ 2 (by decide) w mode depth P h R S a b c e n q x hw
    (InstantiateOperationFrameSyntax.mode_number w mode depth P a b c e R S hf)
    (InstantiateOperationFrameSyntax.metadata w mode depth P a b c e R S hf) hn hc hg hp
  have hs := FormulaTransformBranchSelection.program_iff_selected hZ 4 1 w R S a b c e h n q (fun _ => x) hw ho hg hc
  exact iff_trans (iff_trans hr hb) (.conjI (.conjR hs) (.conjL hs))

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (kind : Fin 4) (x y : Fin m)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  have hp := InstantiateUniformInductionRules.prefix_at_frame w n mode depth P a b c e R S hi hf
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have hb := iff_trans (FormulaTransformStepCorrectness.binary_iff kind w h R S a b c e n q) (SyntaxMixedFormulaCaseTransfer.binary_iff hZ kind w h R S a b c e n q ho oldGraph)
  have hr := SmallModeLogicalFromInduction.binary_iff hZ 2 (by decide) kind w mode depth P h R S a b c e n q x y hw
    (InstantiateOperationFrameSyntax.mode_number w mode depth P a b c e R S hf)
    (InstantiateOperationFrameSyntax.metadata w mode depth P a b c e R S hf) hn hc hg hp
  have hs : Derives Γ ((FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q).iff
      (SyntaxMixedFormulaRecursiveSyntax.binary kind w R S a b c e n q)) := by
    have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact FormulaTransformBranchSelection.program_iff_selected hZ 5 2 w R S a b c e h n q (SyntaxAtomSyntax.two x y) hw ho hg hc
    · exact FormulaTransformBranchSelection.program_iff_selected hZ 6 2 w R S a b c e h n q (SyntaxAtomSyntax.two x y) hw ho hg hc
    · exact FormulaTransformBranchSelection.program_iff_selected hZ 7 2 w R S a b c e h n q (SyntaxAtomSyntax.two x y) hw ho hg hc
    · exact FormulaTransformBranchSelection.program_iff_selected hZ 8 2 w R S a b c e h n q (SyntaxAtomSyntax.two x y) hw ho hg hc
  exact iff_trans (iff_trans hr hb) (.conjI (.conjR hs) (.conjL hs))

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (universal : Bool) (x : Fin m)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have hb := iff_trans (FormulaTransformStepCorrectness.single_iff (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q) (SyntaxMixedFormulaCaseTransfer.single_iff hZ (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q ho oldGraph)
  have hr := InstantiateBinderProgram.quantified_iff hZ universal w n mode depth P a b c e R S h x q hw hi hf hn hc hg
  have hs : Derives Γ ((FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q).iff
      (SyntaxMixedFormulaRecursiveSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w R S a b c e n q)) := by
    cases universal with
    | false => exact FormulaTransformBranchSelection.program_iff_selected hZ 10 1 w R S a b c e h n q (fun _ => x) hw ho hg hc
    | true => exact FormulaTransformBranchSelection.program_iff_selected hZ 9 1 w R S a b c e h n q (fun _ => x) hw ho hg hc
  exact iff_trans (iff_trans hr hb) (.conjI (.conjR hs) (.conjL hs))

theorem single_case_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (tag : Nat) (advance : Bool) (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hs : Derives Γ (FormulaCodeRecursiveSyntax.singleCase tag advance w a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  let B := FormulaCodeRecursiveSyntax.singleCaseBody tag advance w a b n
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 B _ (.conjR hs)
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hi1 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH (old 1 w) (old 1 n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n (old 1)) (HornBinderRules.under_body 1 hi B)
  have hf1 : Derives Δ (InstantiateOperationFrameSyntax.frame (old 1 w) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S (old 1)) (HornBinderRules.under_body 1 hf B)
  have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 a) (old 1 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 1)) (HornBinderRules.under_body 1 hn B)
  have hg1 : Derives Δ (FormulaTransformRecursionSyntax.graph (old 1 w) (old 1 h) (old 1 n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 1)) (HornBinderRules.under_body 1 hg B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht : Derives Δ ((OriginalTransformRowSyntax.run 3 (old 1 w) (old 1 mode) (old 1 depth) (old 1 P) (old 1 n) (old 1 q)).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram (old 1 w) (old 1 R) (old 1 S) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 h) (old 1 n) (old 1 q))) := by
    rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact negation_iff (HornBinderRules.zf_body 1 hZ B) (slot 1 0) (old 1 w) (old 1 n) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S) (old 1 h) (old 1 q) hw1 hi1 hf1 hn1 hg1 (.conjL hB)
    · exact quantified_iff (HornBinderRules.zf_body 1 hZ B) true (slot 1 0) (old 1 w) (old 1 n) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S) (old 1 h) (old 1 q) hw1 hi1 hf1 hn1 hg1 (.conjL hB)
    · exact quantified_iff (HornBinderRules.zf_body 1 hZ B) false (slot 1 0) (old 1 w) (old 1 n) (old 1 mode) (old 1 depth) (old 1 P) (old 1 a) (old 1 b) (old 1 c) (old 1 e) (old 1 R) (old 1 S) (old 1 h) (old 1 q) hw1 hi1 hf1 hn1 hg1 (.conjL hB)
  exact of_eq (by simp only [Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformProgramSyntax.run_rename]) ht

theorem binary_case_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (kind : Fin 4)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hs : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  let B := FormulaCodeRecursiveSyntax.binaryCaseBody kind w a b n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (.conjR hs)
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hi1 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH (old 2 w) (old 2 n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n (old 2)) (HornBinderRules.under_body 2 hi B)
  have hf1 : Derives Δ (InstantiateOperationFrameSyntax.frame (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S (old 2)) (HornBinderRules.under_body 2 hf B)
  have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 2 w) (old 2 n) (old 2 a) (old 2 b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 2)) (HornBinderRules.under_body 2 hn B)
  have hg1 : Derives Δ (FormulaTransformRecursionSyntax.graph (old 2 w) (old 2 h) (old 2 n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 2)) (HornBinderRules.under_body 2 hg B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := binary_iff (HornBinderRules.zf_body 2 hZ B) kind (slot 2 0) (slot 2 1) (old 2 w) (old 2 n) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S) (old 2 h) (old 2 q) hw1 hi1 hf1 hn1 hg1 (.conjL hB)
  exact of_eq (by simp only [Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, FormulaTransformProgramSyntax.run_rename]) ht

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) := by
  have hc := Derives.conjR (.impE (.conjL (FormulaCodeRecursive.recursive_iff hZ w n a b hw)) hn)
  have h0 : Derives Γ ((SyntaxAtomSyntax.atomic w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := SyntaxAtomSyntax.atomic w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact atomic_iff hZ0 w n mode depth P a b c e R S h q hw0 hf0 hn0 hg0 hC
  have h1 : Derives Γ ((FormulaCodeRecursiveSyntax.singleCase 4 false w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.singleCase 4 false w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact single_case_iff hZ0 4 false (Or.inl ⟨rfl, rfl⟩) w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h2 : Derives Γ ((FormulaCodeRecursiveSyntax.binaryCase 0 w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.binaryCase 0 w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact binary_case_iff hZ0 0 w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h3 : Derives Γ ((FormulaCodeRecursiveSyntax.binaryCase 1 w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.binaryCase 1 w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact binary_case_iff hZ0 1 w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h4 : Derives Γ ((FormulaCodeRecursiveSyntax.binaryCase 2 w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.binaryCase 2 w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact binary_case_iff hZ0 2 w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h5 : Derives Γ ((FormulaCodeRecursiveSyntax.binaryCase 3 w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.binaryCase 3 w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact binary_case_iff hZ0 3 w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h6 : Derives Γ ((FormulaCodeRecursiveSyntax.singleCase 9 true w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.singleCase 9 true w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact single_case_iff hZ0 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  have h7 : Derives Γ ((FormulaCodeRecursiveSyntax.singleCase 10 true w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))) := by
    apply Derives.impI
    let C := FormulaCodeRecursiveSyntax.singleCase 10 true w a b n
    let Δ := Context.add C Γ
    have hZ0 := ZFContext.add hZ C
    have hw0 := add hw C
    have hi0 := add hi C
    have hf0 := add hf C
    have hn0 := add hn C
    have hg0 := add hg C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact single_case_iff hZ0 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w n mode depth P a b c e R S h q hw0 hi0 hf0 hn0 hg0 hC
  exact .impE (disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 h7))))))) hc

end PPAC.Migration.Internal.InstantiateFullFormulaProgram
