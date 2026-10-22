import PPAC.Migration.Internal.ObjectSyntaxRenameOperator

/-! 有限纯成员公式RenameFormula；内部自然码守卫、实际集合值求值与实际七字段状态成员。 -/
namespace PPAC.Migration.Internal.SyntaxRenameJudgmentSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxRenameEvaluationSyntax

def body {m} (w r s a b c d n q : Fin m) : Formula (m+1) :=
  (evaluation w.castSucc n.castSucc (Fin.last m)).conj
    (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc)

def renamed {m} (w r s a b c d n q : Fin m) : Formula m := (Formula.mem n w).conj (.ex (body w r s a b c d n q))

theorem renamed_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (renamed w r s a b c d n q).rename ρ = renamed (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [renamed, body, Formula.rename, evaluation_rename, contains_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_renamed {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (hn : Derives Γ (.mem n w)) (hv : Derives Γ (evaluation w n v))
    (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (renamed w r s a b c d n q) := by
  apply Derives.conjI hn
  apply Derives.exI v
  simp only [body, Formula.instantiate, Formula.rename, evaluation_rename, contains_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hv hc

theorem eliminate_renamed {m} {Γ : Context m} (w r s a b c d n q : Fin m) (P : Formula m)
    (hr : Derives Γ (renamed w r s a b c d n q))
    (hc : Derives (Context.add (body w r s a b c d n q) (Context.image Formula.raise Γ)) P.raise) : Derives Γ P :=
  .exE (.conjR hr) hc

theorem reject_code {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hn : Derives Γ (Formula.mem n w).neg) : Derives Γ (renamed w r s a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.conjL (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.SyntaxRenameJudgmentSyntax
