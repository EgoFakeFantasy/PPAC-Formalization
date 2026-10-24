import PPAC.Migration.Internal.ProjectCompilerRootSyntax

/-! A produced compiler output yields an actual parent history and the complete local program. -/
namespace PPAC.Migration.Internal.ProjectCompilerRoot
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerRootSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem certificate_of_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) :
    Derives Γ (certificate w n b q) := by
  let B := ProjectCompilerCodeSyntax.body w n b q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply ProjectCompilerCodeSyntax.eliminate_code w n b q _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have ho := NaturalOrderBasic.ordinal hZ2 w.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL (.conjR hB))
  let V := (ProjectCompilerEvaluationSyntax.evaluation w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))).conj
    (GraphSyntax.edge (Fin.last (m+2)) b.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc)
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (Derives.conjR (Derives.conjR (Derives.conjR hB)))
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have ho3 := of_eq (OrdinalSyntax.ordinal_rename n.castSucc.castSucc Fin.castSucc) (under ho V)
  have hh := ProjectCompilerHistory.from_value (ZFContext.under hZ2 V) w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
    n.castSucc.castSucc.castSucc (Fin.last (m+2)) ho3 (.conjL hV)
  let H := (ProjectCompilerRecursionSyntax.graph w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc).conj
    (ProjectCompilerStateSyntax.state w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last (m+2)).castSucc)
  let Θ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hh
  have hH : Derives Θ H := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under (ZFContext.under hZ2 V) H
  have hc4 : Derives Θ (ProjectCompilerCodeSyntax.carrier w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, ProjectCompilerCodeSyntax.carrier_rename] using under (under (Derives.conjL hB) V) H
  have hv4 : Derives Θ (ProjectCompilerEvaluationSyntax.evaluation w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc) :=
    of_eq (ProjectCompilerEvaluationSyntax.evaluation_rename w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) Fin.castSucc) (under (Derives.conjL hV) H)
  have he4 : Derives Θ (GraphSyntax.edge (Fin.last (m+2)).castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (GraphSyntax.edge_rename (Fin.last (m+2)) b.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc Fin.castSucc) (under (Derives.conjR hV) H)
  have hl := ProjectCompilerStateMembership.local_of_edge hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+3)) (Fin.last (m+2)).castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjR hH) he4
  have hr := assemble w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hc4 hv4 he4 (.conjL hH) (.conjR hH) hl
  exact of_eq (by simp only [Formula.raise, certificate_rename]) hr

end PPAC.Migration.Internal.ProjectCompilerRoot
