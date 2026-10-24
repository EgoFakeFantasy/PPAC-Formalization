import PPAC.Migration.Internal.PacketTokenUniqueSyntax
import PPAC.Migration.Internal.GodelPairArithmetic

/-! Equality transport for actual accepted outputs and addition outputs. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixTransport
open Source SourceAlgebra SourceLogic PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem accepted_output {m} {Γ : Context m} (w n t a b : Fin m) (he : Derives Γ (.equal a b))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (accepted w n t b) := by
  let P := accepted w.castSucc n.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = accepted w n t a := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate b = accepted w n t b := by simp only [P,Formula.instantiate,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ha))

theorem sum_output {m} {Γ : Context m} (w d B y z : Fin m) (he : Derives Γ (.equal y z))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B y)) : Derives Γ (NaturalAdditionSyntax.sum w d B z) := by
  let P := NaturalAdditionSyntax.sum w.castSucc d.castSucc B.castSucc (Fin.last m)
  have h0 : P.instantiate y = NaturalAdditionSyntax.sum w d B y := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate z = NaturalAdditionSyntax.sum w d B z := by simp only [P,Formula.instantiate,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

end PPAC.Migration.Internal.PacketTokenPrefixTransport
