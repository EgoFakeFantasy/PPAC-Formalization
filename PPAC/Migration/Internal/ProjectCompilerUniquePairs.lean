import PPAC.Migration.Internal.ProjectCompilerUniqueMatrices

/-! Two independent EX4 field blocks are eliminated in scalar output comparison. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniquePairs
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerUniqueSyntax ProjectCompilerUniqueMatrixSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem uniform_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a c : Mode)
    (w b z n q r : Fin m) (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (uniformCase a w b z n q)) (hr : Derives Γ (uniformCase c w b z n r)) : Derives Γ (.equal q r) := by
  let A := body a w b z n q
  let Ξ := Context.add A (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 A _ hq
  have hA : Derives Ξ (matrix a (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 q) (slot 4)) := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw A)
  have hI4 := of_eq (allIH_rename w n (old 4)) (HornBinderRules.under_body 4 hI A)
  have hr4 := of_eq (uniformCase_rename c w b z n r (old 4)) (HornBinderRules.under_body 4 hr A)
  let B := body c (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 r)
  let Δ := Context.add B (raisedContext 4 Ξ)
  apply HornBinderRules.eliminate_many 4 B _ hr4
  have hB : Derives Δ (matrix c (old 4 (old 4 w)) (old 4 (old 4 b)) (old 4 (old 4 z)) (old 4 (old 4 n)) (old 4 (old 4 r)) (slot 4)) := .hyp (Or.inl rfl)
  have hw8 := of_eq (omega_rename (old 4 w) (old 4)) (HornBinderRules.under_body 4 hw4 B)
  have hI8 := of_eq (allIH_rename (old 4 w) (old 4 n) (old 4)) (HornBinderRules.under_body 4 hI4 B)
  have hA8 := of_eq (matrix_rename a (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 q) (slot 4) (old 4)) (HornBinderRules.under_body 4 hA B)
  exact ProjectCompilerUniqueMatrices.any_modes (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 4 hZ A) B) a c
    (old 4 (old 4 w)) (old 4 (old 4 b)) (old 4 (old 4 z)) (old 4 (old 4 n)) (old 4 (old 4 q)) (old 4 (old 4 r))
    (fun i => old 4 (slot 4 i)) (slot 4) hw8 hI8 hA8 hB

theorem choices_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z n q r : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (choices w b z n q)) (hr : Derives Γ (choices w b z n r)) : Derives Γ (.equal q r) := by
  apply ProofTreeRootSyntax.disjoin_elim (modes.map (fun mode => uniformCase mode w b z n q)) (.equal q r) hq
  intro X hX
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hX
  apply Derives.impI
  let A := uniformCase a w b z n q
  apply ProofTreeRootSyntax.disjoin_elim (modes.map (fun mode => uniformCase mode w b z n r)) (.equal q r) (add hr A)
  intro Y hY
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hY
  apply Derives.impI
  let B := uniformCase c w b z n r
  let Δ := Context.add B (Context.add A Γ)
  have hA : Derives Δ A := .hyp (Or.inr (Or.inl rfl))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact uniform_unique (ZFContext.add (ZFContext.add hZ A) B) a c w b z n q r (add (add hw A) B) (add (add hI A) B) hA hB

theorem actual_cases_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z n q r : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (ProjectCompilerRecursiveSyntax.casesAt w b z n q))
    (hr : Derives Γ (ProjectCompilerRecursiveSyntax.casesAt w b z n r)) : Derives Γ (.equal q r) :=
  choices_unique hZ w b z n q r hw hI
    (ProjectCompilerUniquePadding.actual_cases_to_choices w b z n q hq)
    (ProjectCompilerUniquePadding.actual_cases_to_choices w b z n r hr)

end PPAC.Migration.Internal.ProjectCompilerUniquePairs
