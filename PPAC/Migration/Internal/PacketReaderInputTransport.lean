import PPAC.Migration.Internal.PacketReaderInputFields

/-! Original object equality aligns actual decoded head/rest before comparing reader steps. -/
namespace PPAC.Migration.Internal.PacketReaderInputTransport
open Source SourceAlgebra SourceLogic PacketReaderStepSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem step_head {m} {Γ : Context m} (w B z o b x v s a r y q c d : Fin m) (he : Derives Γ (.equal b d))
    (hh : Derives Γ (step w B z o b x v s a r y q c)) : Derives Γ (step w B z o d x v s a r y q c) := by
  let P := step w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) x.castSucc v.castSucc s.castSucc a.castSucc r.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate b = step w B z o b x v s a r y q c := by simp only [P,Formula.instantiate,step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate d = step w B z o d x v s a r y q c := by simp only [P,Formula.instantiate,step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem step_rest {m} {Γ : Context m} (w B z o b x v s a r y q c t : Fin m) (he : Derives Γ (.equal x t))
    (hh : Derives Γ (step w B z o b x v s a r y q c)) : Derives Γ (step w B z o b t v s a r y q c) := by
  let P := step w.castSucc B.castSucc z.castSucc o.castSucc b.castSucc (Fin.last m) v.castSucc s.castSucc a.castSucc r.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate x = step w B z o b x v s a r y q c := by simp only [P,Formula.instantiate,step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate t = step w B z o b t v s a r y q c := by simp only [P,Formula.instantiate,step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem reject_head {m} {Γ : Context m} (B z o b s d : Fin m) (he : Derives Γ (.equal b d))
    (hh : Derives Γ (reject B z o b s)) : Derives Γ (reject B z o d s) := by
  let P := reject B.castSucc z.castSucc o.castSucc (Fin.last m) s.castSucc
  have h0 : P.instantiate b = reject B z o b s := by simp only [P,Formula.instantiate,reject_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate d = reject B z o d s := by simp only [P,Formula.instantiate,reject_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

end PPAC.Migration.Internal.PacketReaderInputTransport
