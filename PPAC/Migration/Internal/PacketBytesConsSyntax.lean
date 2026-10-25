import PPAC.Migration.Internal.PacketVarintExecution

/-! Exact tail execution for a given actual Cons keeps the original byte acceptance in the last cell. -/
namespace PPAC.Migration.Internal.PacketBytesConsSyntax
open Source SourceAlgebra SourceLogic PacketBytesTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

def remaining {m} (w h x t a : Fin m) : Formula m := .ex
  ((bytes w.castSucc x.castSucc t.castSucc (Fin.last m)).conj (PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc (Fin.last m) a.castSucc))

theorem remaining_rename {m k} (w h x t a : Fin m) (ρ : Fin m → Fin k) :
    (remaining w h x t a).rename ρ = remaining (ρ w) (ρ h) (ρ x) (ρ t) (ρ a) := by
  simp only [remaining,Formula.rename,bytes_rename,PacketAffineAcceptedSyntax.accepted_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_remaining {m} {Γ : Context m} (w h x t a u : Fin m) (hb : Derives Γ (bytes w x t u))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (remaining w h x t a) := by
  apply Derives.exI u
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,bytes_rename,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hb ha)

end PPAC.Migration.Internal.PacketBytesConsSyntax
