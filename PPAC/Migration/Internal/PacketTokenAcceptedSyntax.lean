import PPAC.Migration.Internal.PacketTokenRootEquation

/-! Actual acceptance is independently defined by a real tagged row and Packet condition. -/
namespace PPAC.Migration.Internal.PacketTokenAcceptedSyntax
open Source SourceAlgebra SourceLogic PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)

def tagAccepted {m} (tag : Nat) (w n t a : Fin m) : Formula m := .ex
  ((tagRow tag w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m)).conj
    (PacketTraceSyntax.condition w.castSucc (Fin.last m)))

def accepted {m} (w n t a : Fin m) : Formula m := tagAccepted 2 w n t a

theorem tagAccepted_rename {m j} (tag : Nat) (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (tagAccepted tag w n t a).rename ρ = tagAccepted tag (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [tagAccepted, Formula.rename, tagRow_rename, PacketTraceSyntax.condition_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem accepted_rename {m j} (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (accepted w n t a).rename ρ = accepted (ρ w) (ρ n) (ρ t) (ρ a) := tagAccepted_rename 2 w n t a ρ

theorem intro_accepted {m} {Γ : Context m} (w n t a r : Fin m) (hr : Derives Γ (row w n t a r))
    (hc : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (accepted w n t a) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PacketTokenSyntax.row, tagRow_rename, PacketTraceSyntax.condition_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.PacketTokenAcceptedSyntax
