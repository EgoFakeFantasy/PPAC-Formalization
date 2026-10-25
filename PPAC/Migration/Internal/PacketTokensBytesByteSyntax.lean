import PPAC.Migration.Internal.PacketTokensBytes
import PPAC.Migration.Internal.StructuralListSpliceByte

/-! One fixed Formula2 says that every actual independent token byte encoding has the original byte-list guard. -/
namespace PPAC.Migration.Internal.PacketTokensBytesByteSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w n : Fin m) : Formula m := .all
  ((PacketTokensBytes.encoded w.castSucc n.castSucc (Fin.last m)).imp (PacketByteInputSyntax.byteList w.castSucc (Fin.last m)))

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def matrix : Formula 2 := property 0 1

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,PacketTokensBytes.encoded_rename,PacketByteInputSyntax.byteList_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by change Fin.lastCases n ρ (Fin.last 1) = n; exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem at_bytes {m} {Γ : Context m} (w n bytes : Fin m) (hp : Derives Γ (property w n))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) : Derives Γ (PacketByteInputSyntax.byteList w bytes) := by
  have hh : Derives Γ ((PacketTokensBytes.encoded w n bytes).imp (PacketByteInputSyntax.byteList w bytes)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,PacketTokensBytes.encoded_rename,PacketByteInputSyntax.byteList_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE bytes hp)
  exact .impE hh he

theorem earlier_at {m} {Γ : Context m} (w n t : Fin m) (hi : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n)) : Derives Γ (property w t) := by
  have hh : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w t))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE t hi)
  exact .impE (.impE hh ht) htn

end PPAC.Migration.Internal.PacketTokensBytesByteSyntax
