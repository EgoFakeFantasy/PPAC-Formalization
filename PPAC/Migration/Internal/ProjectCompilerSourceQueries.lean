import PPAC.Migration.Internal.ProjectCompilerSourceSyntax

/-! Real guarded child queries yield legal source codes, including the actual successor scope. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceQueries
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCaseSyntax ProjectCompilerSourceSyntax
open ProjectSourceCodeSyntax ProjectSourceCodeRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem advanced_source {k m} {Γ : Context m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f x b q : Fin m)
    (hg : Derives Γ (goodQueries P ρ w n f)) (ha : Derives Γ (advanced P ρ n x b q)) :
    Derives Γ (advancedCode w x b f) := by
  let K := (successor (Fin.last m) b.castSucc).conj
    (queried P (fun i => (ρ i).castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) ha
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hg1 := of_eq (goodQueries_rename P ρ w n f Fin.castSucc) (under hg K)
  have ht := query_source P (fun i => (ρ i).castSucc) w.castSucc n.castSucc f.castSucc x.castSucc (Fin.last m) q.castSucc hg1 (.conjR hK)
  apply Derives.exI (t := Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, sourceCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI (.conjL hK) ht)

theorem check_source {k m} {Γ : Context m} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w n f x b q : Fin m) (hg : Derives Γ (goodQueries P ρ w n f))
    (hc : Derives Γ (check advance P ρ n x b q)) : Derives Γ (stepCheck advance w x b f) := by
  cases advance
  · exact query_source P ρ w n f x b q hg hc
  · exact advanced_source P ρ w n f x b q hg hc

theorem check_child_member {k m} {Γ : Context m} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (n x b q : Fin m) (hc : Derives Γ (check advance P ρ n x b q)) : Derives Γ (.mem x n) := by
  cases advance
  · exact .conjL hc
  · let K := (successor (Fin.last m) b.castSucc).conj
      (queried P (fun i => (ρ i).castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add K (Context.image Formula.raise Γ)
    apply Derives.exE (p := K) hc
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    exact .conjL (.conjR hK)

end PPAC.Migration.Internal.ProjectCompilerSourceQueries
