import PPAC.Migration.Internal.ProjectCompilerTypingSyntax

/-! Guarded query typing is preserved through the actual existential successor scope. -/
namespace PPAC.Migration.Internal.ProjectCompilerQueryTyping
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCaseSyntax ProjectCompilerTypingSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem advanced_type {k m} {Γ : Context m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n z x b q : Fin m)
    (hg : Derives Γ (goodQueries P ρ w n z)) (ha : Derives Γ (advanced P ρ n x b q)) :
    Derives Γ (advancedCode w q b z) := by
  let K := (successor (Fin.last m) b.castSucc).conj
    (queried P (fun i => (ρ i).castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) ha
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hg1 := of_eq (goodQueries_rename P ρ w n z Fin.castSucc) (under hg K)
  have ht := query_type P (fun i => (ρ i).castSucc) w.castSucc n.castSucc z.castSucc x.castSucc (Fin.last m) q.castSucc hg1 (.conjR hK)
  apply Derives.exI (t := Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI (.conjL hK) ht)

theorem check_type {k m} {Γ : Context m} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w n z x b q : Fin m) (hg : Derives Γ (goodQueries P ρ w n z))
    (hc : Derives Γ (check advance P ρ n x b q)) : Derives Γ (stepCheck advance w q b z) := by
  cases advance
  · exact query_type P ρ w n z x b q hg hc
  · exact advanced_type P ρ w n z x b q hg hc

end PPAC.Migration.Internal.ProjectCompilerQueryTyping
