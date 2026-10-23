import PPAC.Migration.Internal.ObjectOriginalArgumentFiber

/-! 任意真实候选运行由实际唯一输出纤维取得同一候选的完整Value。 -/
namespace PPAC.Migration.Internal.OriginalArgumentCandidateValue
open Source SourceAlgebra SourceLogic OriginalArgumentValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem output_subst {m} {Γ : Context m} (w mode depth parameter k c d n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hv : Derives Γ (value w mode depth parameter k c d n q)) : Derives Γ (value w mode depth parameter k c d n v) := by
  let P := value w.castSucc mode.castSucc depth.castSucc parameter.castSucc k.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate q = value w mode depth parameter k c d n q := by simp only [P, Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate v = value w mode depth parameter k c d n v := by simp only [P, Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hv))

theorem at_run {m} {Γ : Context m} (w mode depth parameter k c d n q : Fin m)
    (hf : Derives Γ (fiber w mode depth parameter k c d n))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q)) : Derives Γ (value w mode depth parameter k c d n q) := by
  let V := value w.castSucc mode.castSucc depth.castSucc parameter.castSucc k.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hf
  have hr1 : Derives Δ (OriginalTransformRowSyntax.run 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc) := of_eq (OriginalTransformRowSyntax.run_rename 2 w mode depth parameter n q Fin.castSucc) (under hr V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have he := unique _ _ _ _ _ _ _ _ _ _ hV hr1
  exact of_eq (value_rename w mode depth parameter k c d n q Fin.castSucc).symm (output_subst _ _ _ _ _ _ _ _ _ _ (eq_symm he) hV)

end PPAC.Migration.Internal.OriginalArgumentCandidateValue
