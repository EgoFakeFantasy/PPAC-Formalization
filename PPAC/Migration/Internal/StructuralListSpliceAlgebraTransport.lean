import PPAC.Migration.Internal.StructuralListSpliceAlgebraSyntax

/-! Original object equality transports every actual splice argument. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraTransport
open Source SourceAlgebra SourceLogic StructuralListSpliceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem prefix_subst {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal n x))
    (hs : Derives Γ (splice w n t a)) : Derives Γ (splice w x t a) := by
  let P := splice w.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate n = splice w n t a := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = splice w x t a := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem tail {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal t x))
    (hs : Derives Γ (splice w n t a)) : Derives Γ (splice w n x a) := by
  let P := splice w.castSucc n.castSucc (Fin.last m) a.castSucc
  have h0 : P.instantiate t = splice w n t a := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = splice w n x a := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem output {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal a x))
    (hs : Derives Γ (splice w n t a)) : Derives Γ (splice w n t x) := by
  let P := splice w.castSucc n.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = splice w n t a := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = splice w n t x := by simp only [P,Formula.instantiate,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

end PPAC.Migration.Internal.StructuralListSpliceAlgebraTransport
