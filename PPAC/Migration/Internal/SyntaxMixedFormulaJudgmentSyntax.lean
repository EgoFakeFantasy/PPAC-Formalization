import PPAC.Migration.Internal.SyntaxMixedFormulaHistory

/-! 有限纯成员公式MixedFormulaSubst；内部自然码守卫、实际集合值求值与实际七字段状态成员。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentSyntax
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic SyntaxMixedFormulaQuerySyntax SyntaxMixedFormulaEvaluationSyntax

def body {m} (w r s a b c d n q : Fin m) : Formula (m+1) :=
  (evaluation w.castSucc n.castSucc (Fin.last m)).conj
    (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc)

def substituted {m} (w r s a b c d n q : Fin m) : Formula m := (Formula.mem n w).conj (.ex (body w r s a b c d n q))

theorem substituted_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (substituted w r s a b c d n q).rename ρ = substituted (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [substituted, body, Formula.rename, evaluation_rename, contains_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_substituted {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (hn : Derives Γ (.mem n w)) (hv : Derives Γ (evaluation w n v))
    (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (substituted w r s a b c d n q) := by
  apply Derives.conjI hn
  apply Derives.exI v
  simp only [body, Formula.instantiate, Formula.rename, evaluation_rename, contains_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hv hc

theorem eliminate_substituted {m} {Γ : Context m} (w r s a b c d n q : Fin m) (P : Formula m)
    (hr : Derives Γ (substituted w r s a b c d n q))
    (hc : Derives (Context.add (body w r s a b c d n q) (Context.image Formula.raise Γ)) P.raise) : Derives Γ P :=
  .exE (.conjR hr) hc

theorem reject_code {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hn : Derives Γ (Formula.mem n w).neg) : Derives Γ (substituted w r s a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.conjL (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentSyntax
