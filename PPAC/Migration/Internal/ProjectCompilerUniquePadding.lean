import PPAC.Migration.Internal.ProjectCompilerUniqueActualSyntax

/-! Pad unused field slots only inside object EX4; the actual compiler relation is unchanged. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniquePadding
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerUniqueMatrixSyntax ProjectCompilerUniqueActualSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem intro_uniform {m} {Γ : Context m} (mode : Mode) (w b z n q : Fin m) (xs : Fin 4 → Fin m)
    (hc : Derives Γ (matrix mode w b z n q xs)) : Derives Γ (uniformCase mode w b z n q) := by
  apply HornBinderRules.intro_many 4 (body mode w b z n q) xs
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hc

theorem from_actual_mode {m} {Γ : Context m} (mode : Mode) (w b z n q : Fin m)
    (hc : Derives Γ (actualCase mode w b z n q)) : Derives Γ (uniformCase mode w b z n q) := by
  cases mode
  · exact intro_uniform .falseCase w b z n q (fun _ => w) hc
  · exact intro_uniform .trueCase w b z n q (fun _ => w) hc
  · let B := ProjectCompilerCaseSyntax.atomicBody 0 w b z n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .memberCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .memberCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .memberCase w b z n q (old 2)).symm ho
  · let B := ProjectCompilerCaseSyntax.atomicBody 1 w b z n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .equalCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .equalCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .equalCase w b z n q (old 2)).symm ho
  · let B := ProjectCompilerCaseSyntax.atomicBody 2 w b z n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .subsetCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .subsetCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .subsetCase w b z n q (old 2)).symm ho
  · let B := ProjectCompilerCaseSyntax.singleBody 4 false ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w b n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .negCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .negCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .negCase w b z n q (old 2)).symm ho
  · exact hc
  · exact hc
  · exact hc
  · exact hc
  · let B := ProjectCompilerCaseSyntax.singleBody 9 true ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w b n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .forallCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .forallCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .forallCase w b z n q (old 2)).symm ho
  · let B := ProjectCompilerCaseSyntax.singleBody 10 true ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w b n q
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm : Derives Δ (matrix .existsCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q)
        (ProjectCompilerCaseIntro.four (slot 2 0) (slot 2 1) (old 2 w) (old 2 w))) := hB
    have ho := intro_uniform .existsCase (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) _ hm
    exact of_eq (uniformCase_rename .existsCase w b z n q (old 2)).symm ho

theorem choose_mode {m} {Γ : Context m} (mode : Mode) (w b z n q : Fin m)
    (hc : Derives Γ (actualCase mode w b z n q)) : Derives Γ (choices w b z n q) :=
  ProofTreeRootSyntax.disjoin_intro (modes.map (fun mode => uniformCase mode w b z n q)) (uniformCase mode w b z n q)
    (List.mem_map.mpr ⟨mode, mode_mem mode, rfl⟩) (from_actual_mode mode w b z n q hc)

theorem actual_cases_to_choices {m} {Γ : Context m} (w b z n q : Fin m)
    (hc : Derives Γ (ProjectCompilerRecursiveSyntax.casesAt w b z n q)) : Derives Γ (choices w b z n q) := by
  have h0 : Derives Γ ((actualCase .falseCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .falseCase w b z n q (.hyp (Or.inl rfl))
  have h1 : Derives Γ ((actualCase .trueCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .trueCase w b z n q (.hyp (Or.inl rfl))
  have h2 : Derives Γ ((actualCase .memberCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .memberCase w b z n q (.hyp (Or.inl rfl))
  have h3 : Derives Γ ((actualCase .equalCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .equalCase w b z n q (.hyp (Or.inl rfl))
  have h4 : Derives Γ ((actualCase .subsetCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .subsetCase w b z n q (.hyp (Or.inl rfl))
  have h5 : Derives Γ ((actualCase .negCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .negCase w b z n q (.hyp (Or.inl rfl))
  have h6 : Derives Γ ((actualCase .conjCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .conjCase w b z n q (.hyp (Or.inl rfl))
  have h7 : Derives Γ ((actualCase .disjCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .disjCase w b z n q (.hyp (Or.inl rfl))
  have h8 : Derives Γ ((actualCase .impCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .impCase w b z n q (.hyp (Or.inl rfl))
  have h9 : Derives Γ ((actualCase .iffCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .iffCase w b z n q (.hyp (Or.inl rfl))
  have h10 : Derives Γ ((actualCase .forallCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .forallCase w b z n q (.hyp (Or.inl rfl))
  have h11 : Derives Γ ((actualCase .existsCase w b z n q).imp (choices w b z n q)) := by
    apply Derives.impI
    exact choose_mode .existsCase w b z n q (.hyp (Or.inl rfl))
  exact .impE (FormulaCodeCaseLogic.disj_imp h0 (FormulaCodeCaseLogic.disj_imp h1 (FormulaCodeCaseLogic.disj_imp h2 (FormulaCodeCaseLogic.disj_imp h3 (FormulaCodeCaseLogic.disj_imp h4 (FormulaCodeCaseLogic.disj_imp h5 (FormulaCodeCaseLogic.disj_imp h6 (FormulaCodeCaseLogic.disj_imp h7 (FormulaCodeCaseLogic.disj_imp h8 (FormulaCodeCaseLogic.disj_imp h9 (FormulaCodeCaseLogic.disj_imp h10 h11))))))))))) hc

end PPAC.Migration.Internal.ProjectCompilerUniquePadding
