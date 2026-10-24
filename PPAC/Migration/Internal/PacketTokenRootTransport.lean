import PPAC.Migration.Internal.ObjectPacketToken

/-! Original object equality substitutes each ordered field of a real tagged entry. -/
namespace PPAC.Migration.Internal.PacketTokenRootTransport
open Source SourceAlgebra SourceLogic PacketTokenSyntax

theorem entry_first {m} {Γ : Context m} (tag : Nat) (w V a b c u : Fin m)
    (he : Derives Γ (.equal a u)) (hh : Derives Γ (tagEntry tag w V a b c)) : Derives Γ (tagEntry tag w V u b c) := by
  let P := tagEntry tag w.castSucc V.castSucc (Fin.last m) b.castSucc c.castSucc
  have h0 : P.instantiate a = tagEntry tag w V a b c := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = tagEntry tag w V u b c := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem entry_second {m} {Γ : Context m} (tag : Nat) (w V a b c u : Fin m)
    (he : Derives Γ (.equal b u)) (hh : Derives Γ (tagEntry tag w V a b c)) : Derives Γ (tagEntry tag w V a u c) := by
  let P := tagEntry tag w.castSucc V.castSucc a.castSucc (Fin.last m) c.castSucc
  have h0 : P.instantiate b = tagEntry tag w V a b c := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = tagEntry tag w V a u c := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem entry_third {m} {Γ : Context m} (tag : Nat) (w V a b c u : Fin m)
    (he : Derives Γ (.equal c u)) (hh : Derives Γ (tagEntry tag w V a b c)) : Derives Γ (tagEntry tag w V a b u) := by
  let P := tagEntry tag w.castSucc V.castSucc a.castSucc b.castSucc (Fin.last m)
  have h0 : P.instantiate c = tagEntry tag w V a b c := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = tagEntry tag w V a b u := by
    simp only [P, Formula.instantiate, tagEntry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

end PPAC.Migration.Internal.PacketTokenRootTransport
