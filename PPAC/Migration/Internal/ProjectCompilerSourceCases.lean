import PPAC.Migration.Internal.ProjectCompilerSourceMatrix

/-! Actual compiler case witnesses are eliminated when recovering the complete source grammar. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceCases
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerRecursiveSyntax ProjectCompilerSourceSyntax ProjectCompilerUniqueMatrixSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem uniform_source_cases {m} {Γ : Context m} (mode : Mode) (w b z n q f : Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f)) (hg : Derives Γ (goodQueries codeMatrix (parameters w) w n f))
    (hc : Derives Γ (uniformCase mode w b z n q)) : Derives Γ (ProjectSourceCodeRecursiveSyntax.allCases w n b f) := by
  let B := ProjectCompilerUniqueMatrixSyntax.body mode w b z n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hctx4 := of_eq (SyntaxTermSyntax.contexts_rename w b f (old 4)) (HornBinderRules.under_body 4 hctx B)
  have hg4 := of_eq (goodQueries_rename codeMatrix (parameters w) w n f (old 4)) (HornBinderRules.under_body 4 hg B)
  have ho := ProjectCompilerSourceMatrix.mode_source_cases mode (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 q) (old 4 f) (slot 4) hctx4 hg4 hB
  exact of_eq (ProjectSourceCodeRecursiveSyntax.allCases_rename w n b f (old 4)).symm ho

theorem choices_source_cases {m} {Γ : Context m} (w b z n q f : Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f)) (hg : Derives Γ (goodQueries codeMatrix (parameters w) w n f))
    (hc : Derives Γ (choices w b z n q)) : Derives Γ (ProjectSourceCodeRecursiveSyntax.allCases w n b f) := by
  apply ProofTreeRootSyntax.disjoin_elim (modes.map (fun mode => uniformCase mode w b z n q)) (ProjectSourceCodeRecursiveSyntax.allCases w n b f) hc
  intro X hX
  obtain ⟨mode,_,rfl⟩ := List.mem_map.mp hX
  apply Derives.impI
  exact uniform_source_cases mode w b z n q f (add hctx _) (add hg _) (.hyp (Or.inl rfl))

theorem actual_source_cases {m} {Γ : Context m} (w b z n q f : Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f)) (hg : Derives Γ (goodQueries codeMatrix (parameters w) w n f))
    (hc : Derives Γ (casesAt w b z n q)) : Derives Γ (ProjectSourceCodeRecursiveSyntax.allCases w n b f) :=
  choices_source_cases w b z n q f hctx hg (ProjectCompilerUniquePadding.actual_cases_to_choices w b z n q hc)

end PPAC.Migration.Internal.ProjectCompilerSourceCases
