import PPAC.Migration.Internal.StructuralListSpliceTraceProperties

/-! Original equality substitution transports the independent fold graph. -/
namespace PPAC.Migration.Internal.StructuralListSpliceTraceTransport
open Source SourceAlgebra SourceLogic StructuralListSpliceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_subst {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal n x))
    (hf : Derives Γ (raw w n t a)) : Derives Γ (raw w x t a) := by
  let P := raw w.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate n = raw w n t a := by simp only [P,Formula.instantiate,raw_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = raw w x t a := by simp only [P,Formula.instantiate,raw_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hf))

theorem output_subst {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal a x))
    (hf : Derives Γ (raw w n t a)) : Derives Γ (raw w n t x) := by
  let P := raw w.castSucc n.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = raw w n t a := by simp only [P,Formula.instantiate,raw_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = raw w n t x := by simp only [P,Formula.instantiate,raw_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hf))

end PPAC.Migration.Internal.StructuralListSpliceTraceTransport
