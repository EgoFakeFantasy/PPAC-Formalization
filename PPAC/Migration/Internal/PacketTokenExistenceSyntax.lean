import PPAC.Migration.Internal.PacketTokenByteBounds

/-! Existence quantifies all internal tails and outputs of the independently defined real token run. -/
namespace PPAC.Migration.Internal.PacketTokenExistenceSyntax
open Source SourceAlgebra SourceLogic PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def existsOutput {m} (w n t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (accepted w.castSucc n.castSucc t.castSucc (Fin.last m)))

def property {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (existsOutput w.castSucc n.castSucc (Fin.last m)))

def matrix : Formula 2 := property 0 1

theorem existsOutput_rename {m j} (w n t : Fin m) (ρ : Fin m → Fin j) :
    (existsOutput w n t).rename ρ = existsOutput (ρ w) (ρ n) (ρ t) := by
  simp only [existsOutput,Formula.rename,accepted_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem property_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,existsOutput_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem property_at {m} {Γ : Context m} (w n t : Fin m) (hp : Derives Γ (property w n)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsOutput w n t) := by
  have hi : Derives Γ ((Formula.mem t w).imp (existsOutput w n t)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,existsOutput_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE t hp)
  exact .impE hi ht

theorem intro_output {m} {Γ : Context m} (w n t a : Fin m) (ha : Derives Γ (.mem a w)) (ht : Derives Γ (accepted w n t a)) :
    Derives Γ (existsOutput w n t) := by
  apply Derives.exI a
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI ha ht)

end PPAC.Migration.Internal.PacketTokenExistenceSyntax
