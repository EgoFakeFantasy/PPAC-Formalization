import PPAC.Migration.Internal.PacketTokenExistenceInduction

/-! Equality aligns actual recursive token inputs and their real shift sums. -/
namespace PPAC.Migration.Internal.PacketTokenValueTransport
open Source SourceAlgebra SourceLogic PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem accepted_input {m} {Γ : Context m} (w n t a q : Fin m) (he : Derives Γ (.equal n q))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (accepted w q t a) := by
  let P := accepted w.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate n = accepted w n t a := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = accepted w q t a := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ha))

theorem sum_first {m} {Γ : Context m} (w d B y e : Fin m) (he : Derives Γ (.equal d e))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B y)) : Derives Γ (NaturalAdditionSyntax.sum w e B y) := by
  let P := NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc y.castSucc
  have h0 : P.instantiate d = NaturalAdditionSyntax.sum w d B y := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate e = NaturalAdditionSyntax.sum w e B y := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

end PPAC.Migration.Internal.PacketTokenValueTransport
