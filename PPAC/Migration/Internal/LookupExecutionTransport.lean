import PPAC.Migration.Internal.HornVariableValue

/-! 已验收查找执行关系的参数／索引／输出等词传输，保持原执行定义。 -/
namespace PPAC.Migration.Internal.LookupExecutionTransport
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem parameter_subst {m} {Γ : Context m} (w n n' i y : Fin m) (he : Derives Γ (.equal n n'))
    (hx : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (LookupTableExecutionSyntax.executed w n' i y) := by
  let P := LookupTableExecutionSyntax.executed w.castSucc (Fin.last m) i.castSucc y.castSucc
  have h0 : P.instantiate n = LookupTableExecutionSyntax.executed w n i y := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate n' = LookupTableExecutionSyntax.executed w n' i y := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

theorem index_subst {m} {Γ : Context m} (w n i i' y : Fin m) (he : Derives Γ (.equal i i'))
    (hx : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (LookupTableExecutionSyntax.executed w n i' y) := by
  let P := LookupTableExecutionSyntax.executed w.castSucc n.castSucc (Fin.last m) y.castSucc
  have h0 : P.instantiate i = LookupTableExecutionSyntax.executed w n i y := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate i' = LookupTableExecutionSyntax.executed w n i' y := by simp only [P, Formula.instantiate, LookupTableExecutionSyntax.executed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

theorem fields_subst {m} {Γ : Context m} (w n n' i i' y y' : Fin m)
    (hn : Derives Γ (.equal n n')) (hi : Derives Γ (.equal i i')) (hy : Derives Γ (.equal y y'))
    (hx : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (LookupTableExecutionSyntax.executed w n' i' y') :=
  HornLookupRowSyntax.execution_value_subst _ _ _ _ _ hy (index_subst _ _ _ _ _ hi (parameter_subst _ _ _ _ _ hn hx))

end PPAC.Migration.Internal.LookupExecutionTransport
