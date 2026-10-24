import PPAC.Migration.Internal.PacketBytesExecutionSyntax

/-! Original equality substitution aligns actual recursive list inputs and affine cells. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionTransport
open Source SourceAlgebra SourceLogic PacketBytesTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_subst {m} {Γ : Context m} (w n t a x : Fin m) (he : Derives Γ (.equal n x))
    (hb : Derives Γ (bytes w n t a)) : Derives Γ (bytes w x t a) := by
  let P := bytes w.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate n = bytes w n t a := by simp only [P,Formula.instantiate,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate x = bytes w x t a := by simp only [P,Formula.instantiate,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hb))

theorem affine_digit {m} {Γ : Context m} (w h u a d : Fin m) (he : Derives Γ (.equal h d))
    (hb : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (PacketAffineAcceptedSyntax.accepted true w d u a) := by
  let P := PacketAffineAcceptedSyntax.accepted true w.castSucc (Fin.last m) u.castSucc a.castSucc
  have h0 : P.instantiate h = PacketAffineAcceptedSyntax.accepted true w h u a := by simp only [P,Formula.instantiate,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate d = PacketAffineAcceptedSyntax.accepted true w d u a := by simp only [P,Formula.instantiate,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hb))

theorem affine_tail {m} {Γ : Context m} (w h u a v : Fin m) (he : Derives Γ (.equal u v))
    (hb : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h v a) := by
  let P := PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc (Fin.last m) a.castSucc
  have h0 : P.instantiate u = PacketAffineAcceptedSyntax.accepted true w h u a := by simp only [P,Formula.instantiate,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate v = PacketAffineAcceptedSyntax.accepted true w h v a := by simp only [P,Formula.instantiate,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hb))

end PPAC.Migration.Internal.PacketBytesExecutionTransport
