import PPAC.Migration.Internal.ProjectCompilerHistory

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerJudgmentSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxTermSyntax ProjectCompilerEvaluationSyntax

def atCarrier {m} (w c n b f : Fin m) : Formula m :=
  (Formula.mem n w).conj ((contexts w b f).conj (.ex
    ((evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc))))

theorem atCarrier_rename {m k} (w c n b f : Fin m) (r : Fin m → Fin k) :
    (atCarrier w c n b f).rename r = atCarrier (r w) (r c) (r n) (r b) (r f) := by
  simp only [atCarrier, Formula.rename, contexts_rename, evaluation_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_atCarrier {m} {Γ : Context m} (w c n b f v : Fin m) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (contexts w b f)) (hv : Derives Γ (evaluation w c n v)) (he : Derives Γ (edge v b f)) :
    Derives Γ (atCarrier w c n b f) := by
  apply Derives.conjI hn
  apply Derives.conjI hc
  apply Derives.exI v
  simp only [Formula.instantiate, Formula.rename, evaluation_rename, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hv he

theorem eliminate_atCarrier {m} {Γ : Context m} (w c n b f : Fin m) (q : Formula m) (ht : Derives Γ (atCarrier w c n b f))
    (hc : Derives (Context.add
      ((evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc))
      (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE (.conjR (.conjR ht)) hc

theorem reject_code {m} {Γ : Context m} (w c n b f : Fin m) (hn : Derives Γ (Formula.mem n w).neg) :
    Derives Γ (atCarrier w c n b f).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.conjL (.hyp (Or.inl rfl)))

theorem reject_context {m} {Γ : Context m} (w c n b f : Fin m) (hn : Derives Γ (contexts w b f).neg) :
    Derives Γ (atCarrier w c n b f).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.conjL (.conjR (.hyp (Or.inl rfl))))
end PPAC.Migration.Internal.ProjectCompilerJudgmentSyntax
