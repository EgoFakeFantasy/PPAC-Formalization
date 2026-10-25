import PPAC.Migration.Internal.PacketTokensBytesRecursionSyntax

/-! Original object equality transports a shared-head seeded Cons cell. -/
namespace PPAC.Migration.Internal.PacketTokensBytesPushTransport
open Source SourceAlgebra SourceLogic PacketTokensBytesRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem output {m} {Γ : Context m} (w h t a b : Fin m) (he : Derives Γ (.equal a b))
    (hp : Derives Γ (push w h t a)) : Derives Γ (push w h t b) := by
  let P := push w.castSucc h.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = push w h t a := by simp only [P,Formula.instantiate,push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate b = push w h t b := by simp only [P,Formula.instantiate,push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem head {m} {Γ : Context m} (w h k t a : Fin m) (he : Derives Γ (.equal h k))
    (hp : Derives Γ (push w h t a)) : Derives Γ (push w k t a) := by
  let P := push w.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate h = push w h t a := by simp only [P,Formula.instantiate,push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate k = push w k t a := by simp only [P,Formula.instantiate,push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

end PPAC.Migration.Internal.PacketTokensBytesPushTransport
