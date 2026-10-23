import PPAC.Migration.Internal.FormulaTransformRootStep
import PPAC.Migration.Internal.FormulaAtomicProgramSyntax

/-! 真实完整程序在已知源构造器处精确筛选，原子子程序保持全十一分支边界。 -/
namespace PPAC.Migration.Internal.FormulaTransformBranchSelection
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open OriginalAtomicRunDispatch (disj_imp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem program_iff_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11) (arity : Nat)
    (w R S a b c d h n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n)) :
    Derives Γ ((FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q).iff
      (SyntaxMixedFormulaTagCases.tagBranch kind w R S a b c d n q)) := by
  have oldGraph := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h n hw)) hg
  have hp := iff_trans (FormulaTransformStepCorrectness.program_iff hZ w R S a b c d h n q hw)
    (SyntaxMixedFormulaLocalTransfer.all_iff hZ w R S a b c d h n q ho oldGraph)
  have hf : Derives Γ ((SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q).iff
      (SyntaxMixedFormulaTagCases.tagBranch kind w R S a b c d n q)) := by
    apply Derives.conjI
    · apply Derives.impI
      exact SyntaxMixedFormulaTagCases.filter (ZFContext.add hZ _) kind arity w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact SyntaxMixedFormulaBranchIntro.intro_cases kind w R S a b c d n q (.hyp (Or.inl rfl))
  exact iff_trans hp hf

theorem full_from_atomic {m} {Γ : Context m} (w R S a b c d h n q : Fin m)
    (hp : Derives Γ (FormulaAtomicProgramSyntax.run w R S a b c d n q)) :
    Derives Γ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q) := by
  apply Derives.disjE hp
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.disjL (.hyp (Or.inl rfl)))
    · exact .disjR (.disjR (.disjL (.hyp (Or.inl rfl))))

theorem atomic_from_full_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (arity : Nat)
    (w R S a b c d h n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n))
    (hp : Derives Γ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)) :
    Derives Γ (FormulaAtomicProgramSyntax.run w R S a b c d n q) := by
  have hs := Derives.impE (.conjL (program_iff_selected hZ ⟨kind.val, by omega⟩ arity w R S a b c d h n q xs hw ho hg hc)) hp
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact .disjL (.disjL hs)
  · exact .disjL (.disjR hs)
  · exact .disjR (.disjL (.impE (.conjR (FormulaTransformAtomCorrectness.membership_iff hZ w R S a b c d n q hw)) hs))
  · exact .disjR (.disjR (.impE (.conjR (FormulaTransformAtomCorrectness.equality_iff hZ w R S a b c d n q hw)) hs))

theorem atomic_from_full {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d h n q : Fin m) (hw : Derives Γ (omega w)) (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n))
    (hp : Derives Γ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)) :
    Derives Γ (FormulaAtomicProgramSyntax.run w R S a b c d n q) := by
  have h0 : Derives Γ ((SyntaxAtomSyntax.nullary false w a b n).imp (FormulaAtomicProgramSyntax.run w R S a b c d n q)) := by
    apply Derives.impI
    exact atomic_from_full_at (ZFContext.add hZ _) 0 0 w R S a b c d h n q Fin.elim0 (add hw _) (add ho _) (add hg _) (.conjR (.hyp (Or.inl rfl))) (add hp _)
  have h1 : Derives Γ ((SyntaxAtomSyntax.nullary true w a b n).imp (FormulaAtomicProgramSyntax.run w R S a b c d n q)) := by
    apply Derives.impI
    exact atomic_from_full_at (ZFContext.add hZ _) 1 0 w R S a b c d h n q Fin.elim0 (add hw _) (add ho _) (add hg _) (.conjR (.hyp (Or.inl rfl))) (add hp _)
  have h2 : Derives Γ ((SyntaxAtomSyntax.membership w a b n).imp (FormulaAtomicProgramSyntax.run w R S a b c d n q)) := by
    apply Derives.impI
    let A := SyntaxAtomSyntax.membership w a b n
    let Ξ := Context.add A Γ
    let B := SyntaxAtomSyntax.memberBody w a b n
    let Δ := Context.add B (raisedContext 3 Ξ)
    apply HornBinderRules.eliminate_many 3 B _ (.conjR (.hyp (Or.inl rfl) : Derives Ξ A))
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 (add hw A) B)
    have ho1 : Derives Δ (OrdinalSyntax.ordinal (old 3 n)) := of_eq (OrdinalSyntax.ordinal_rename n (old 3)) (HornBinderRules.under_body 3 (add ho A) B)
    have hg1 : Derives Δ (FormulaTransformRecursionSyntax.graph (old 3 w) (old 3 h) (old 3 n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 3)) (HornBinderRules.under_body 3 (add hg A) B)
    have hp1 : Derives Δ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 d) (old 3 h) (old 3 n) (old 3 q)) := of_eq (FormulaTransformProgramSyntax.run_rename _ w R S a b c d h n q (old 3)) (HornBinderRules.under_body 3 (add hp A) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := atomic_from_full_at (HornBinderRules.zf_body 3 (ZFContext.add hZ A) B) 2 3 (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 d) (old 3 h) (old 3 n) (old 3 q) (SyntaxAtomSyntax.three (slot 3 0) (slot 3 1) (slot 3 2)) hw1 ho1 hg1 (.conjR hB) hp1
    exact of_eq (FormulaAtomicProgramSyntax.run_rename w R S a b c d n q (old 3)).symm ht
  have h3 : Derives Γ ((SyntaxAtomSyntax.equality w a b n).imp (FormulaAtomicProgramSyntax.run w R S a b c d n q)) := by
    apply Derives.impI
    let A := SyntaxAtomSyntax.equality w a b n
    let Ξ := Context.add A Γ
    let B := SyntaxAtomSyntax.equalBody w a b n
    let Δ := Context.add B (raisedContext 2 Ξ)
    apply HornBinderRules.eliminate_many 2 B _ (.conjR (.hyp (Or.inl rfl) : Derives Ξ A))
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw A) B)
    have ho1 : Derives Δ (OrdinalSyntax.ordinal (old 2 n)) := of_eq (OrdinalSyntax.ordinal_rename n (old 2)) (HornBinderRules.under_body 2 (add ho A) B)
    have hg1 : Derives Δ (FormulaTransformRecursionSyntax.graph (old 2 w) (old 2 h) (old 2 n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 2)) (HornBinderRules.under_body 2 (add hg A) B)
    have hp1 : Derives Δ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 h) (old 2 n) (old 2 q)) := of_eq (FormulaTransformProgramSyntax.run_rename _ w R S a b c d h n q (old 2)) (HornBinderRules.under_body 2 (add hp A) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := atomic_from_full_at (HornBinderRules.zf_body 2 (ZFContext.add hZ A) B) 3 2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 h) (old 2 n) (old 2 q) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1)) hw1 ho1 hg1 (.conjR hB) hp1
    exact of_eq (FormulaAtomicProgramSyntax.run_rename w R S a b c d n q (old 2)).symm ht
  exact .impE (disj_imp (disj_imp h0 h1) (disj_imp h2 h3)) ha

theorem atomic_program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d h n q : Fin m) (hw : Derives Γ (omega w)) (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((FormulaAtomicProgramSyntax.run w R S a b c d n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact full_from_atomic w R S a b c d h n q (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact atomic_from_full (ZFContext.add hZ _) w R S a b c d h n q (add hw _) (add ho _) (add hg _) (add ha _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.FormulaTransformBranchSelection
