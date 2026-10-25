import PPAC.Migration.Internal.PacketReaderConsumptionStopping
import PPAC.Migration.Internal.StructuralListLengthConstruct

/-! Actual remaining input length and a fixed Formula4 for internal length conservation. -/
namespace PPAC.Migration.Internal.PacketReaderLengthSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderConsumptionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open NaturalAdditionSyntax (sum sum_rename)
open SyntaxRenameQuerySyntax (of_eq)

def lengthAt {m} (w f i a : Fin m) : Formula m := .ex
  ((inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).conj (hasLength w.castSucc (Fin.last m) a.castSucc))
def existsLengthAt {m} (w f i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (lengthAt w.castSucc f.castSucc i.castSucc (Fin.last m)))
def balance {m} (w f N i : Fin m) : Formula m := .all
  ((lengthAt w.castSucc f.castSucc i.castSucc (Fin.last m)).imp (sum w.castSucc i.castSucc (Fin.last m) N.castSucc))
def matrix : Formula 4 := balance 0 1 2 3
def allBalance {m} (w f N : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (balance w.castSucc f.castSucc N.castSucc (Fin.last m)))

theorem lengthAt_rename {m k} (w f i a : Fin m) (ρ : Fin m → Fin k) :
    (lengthAt w f i a).rename ρ = lengthAt (ρ w) (ρ f) (ρ i) (ρ a) := by
  simp only [lengthAt,Formula.rename,inputAt_rename,hasLength_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem existsLengthAt_rename {m k} (w f i : Fin m) (ρ : Fin m → Fin k) :
    (existsLengthAt w f i).rename ρ = existsLengthAt (ρ w) (ρ f) (ρ i) := by
  simp only [existsLengthAt,Formula.rename,lengthAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem balance_rename {m k} (w f N i : Fin m) (ρ : Fin m → Fin k) :
    (balance w f N i).rename ρ = balance (ρ w) (ρ f) (ρ N) (ρ i) := by
  simp only [balance,Formula.rename,lengthAt_rename,sum_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem allBalance_rename {m k} (w f N : Fin m) (ρ : Fin m → Fin k) :
    (allBalance w f N).rename ρ = allBalance (ρ w) (ρ f) (ρ N) := by
  simp only [allBalance,Formula.rename,balance_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 3 → Fin m) (i : Fin m) : MinimalPredicates.pred matrix ρ i = balance (ρ 0) (ρ 1) (ρ 2) i := by
  have h0 : Fin.lastCases i ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases i ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases i ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases i ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases i ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases i ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases i ρ (3 : Fin 4) = i := by
    change Fin.lastCases i ρ (Fin.last 3) = i
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,balance_rename,h0,h1,h2,h3]

theorem intro_length {m} {Γ : Context m} (w f i a L : Fin m) (hL : Derives Γ (inputAt w f i L))
    (ha : Derives Γ (hasLength w L a)) : Derives Γ (lengthAt w f i a) := by
  apply Derives.exI L
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,inputAt_rename,hasLength_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hL ha)

theorem balance_at {m} {Γ : Context m} (w f N i a : Fin m) (hb : Derives Γ (balance w f N i))
    (ha : Derives Γ (lengthAt w f i a)) : Derives Γ (sum w i a N) := by
  have hp : Derives Γ ((lengthAt w f i a).imp (sum w i a N)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,lengthAt_rename,sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE a hb)
  exact .impE hp ha

theorem all_at {m} {Γ : Context m} (w f N i : Fin m) (hb : Derives Γ (allBalance w f N))
    (hi : Derives Γ (.mem i w)) : Derives Γ (balance w f N i) := by
  have hp : Derives Γ ((Formula.mem i w).imp (balance w f N i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,balance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hb)
  exact .impE hp hi

end PPAC.Migration.Internal.PacketReaderLengthSyntax
