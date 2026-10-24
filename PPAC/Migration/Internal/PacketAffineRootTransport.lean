import PPAC.Migration.Internal.ObjectPacketClosedTrace

/-! Equality transport for exact Packet rows and real trace entries; no semantic evaluation. -/
namespace PPAC.Migration.Internal.PacketAffineRootTransport
open Source SourceAlgebra SourceLogic PacketHornAffineSyntax

theorem row_digit {m} {Γ : Context m} (wide : Bool) (w d t n r u : Fin m)
    (he : Derives Γ (.equal d u)) (hh : Derives Γ (row wide w d t n r)) : Derives Γ (row wide w u t n r) := by
  let P := row wide w.castSucc (Fin.last m) t.castSucc n.castSucc r.castSucc
  have h0 : P.instantiate d = row wide w d t n r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = row wide w u t n r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem row_tail {m} {Γ : Context m} (wide : Bool) (w d t n r u : Fin m)
    (he : Derives Γ (.equal t u)) (hh : Derives Γ (row wide w d t n r)) : Derives Γ (row wide w d u n r) := by
  let P := row wide w.castSucc d.castSucc (Fin.last m) n.castSucc r.castSucc
  have h0 : P.instantiate t = row wide w d t n r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = row wide w d u n r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem row_output {m} {Γ : Context m} (wide : Bool) (w d t n r u : Fin m)
    (he : Derives Γ (.equal n u)) (hh : Derives Γ (row wide w d t n r)) : Derives Γ (row wide w d t u r) := by
  let P := row wide w.castSucc d.castSucc t.castSucc (Fin.last m) r.castSucc
  have h0 : P.instantiate n = row wide w d t n r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = row wide w d t u r := by
    simp only [P, Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem entry_digit {m} {Γ : Context m} (wide : Bool) (w V d t n u : Fin m)
    (he : Derives Γ (.equal d u)) (hh : Derives Γ (entry wide w V d t n)) : Derives Γ (entry wide w V u t n) := by
  let P := entry wide w.castSucc V.castSucc (Fin.last m) t.castSucc n.castSucc
  have h0 : P.instantiate d = entry wide w V d t n := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = entry wide w V u t n := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem entry_tail {m} {Γ : Context m} (wide : Bool) (w V d t n u : Fin m)
    (he : Derives Γ (.equal t u)) (hh : Derives Γ (entry wide w V d t n)) : Derives Γ (entry wide w V d u n) := by
  let P := entry wide w.castSucc V.castSucc d.castSucc (Fin.last m) n.castSucc
  have h0 : P.instantiate t = entry wide w V d t n := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = entry wide w V d u n := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

theorem entry_output {m} {Γ : Context m} (wide : Bool) (w V d t n u : Fin m)
    (he : Derives Γ (.equal n u)) (hh : Derives Γ (entry wide w V d t n)) : Derives Γ (entry wide w V d t u) := by
  let P := entry wide w.castSucc V.castSucc d.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate n = entry wide w V d t n := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate u = entry wide w V d t u := by
    simp only [P, Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact SyntaxRenameQuerySyntax.of_eq h1 (Derives.eqSubst P he (SyntaxRenameQuerySyntax.of_eq h0.symm hh))

end PPAC.Migration.Internal.PacketAffineRootTransport
