import PPAC.Migration.Internal.PacketBytesExecution

/-! Independent LEB128 cells: the terminal is the first cons over Nil; a continuation has nonzero prior value. -/
namespace PPAC.Migration.Internal.PacketVarintCellSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def terminal {m} (w B x h u v : Fin m) : Formula m := (StructuralListSyntax.nilCode w x).conj
  ((empty u).conj ((Formula.mem h B).conj (.equal v h)))

def continuation {m} (w B h u v : Fin m) : Formula m := .ex
  ((empty u.castSucc).neg.conj ((PacketAffineSyntax.affine w.castSucc B.castSucc (Fin.last m) u.castSucc v.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) B.castSucc h.castSucc)))

def cell {m} (w B x h u v : Fin m) : Formula m := (Formula.mem h w).conj ((Formula.mem u w).conj
  ((Formula.mem v w).conj ((terminal w B x h u v).disj (continuation w B h u v))))

theorem terminal_rename {m k} (w B x h u v : Fin m) (ρ : Fin m → Fin k) :
    (terminal w B x h u v).rename ρ = terminal (ρ w) (ρ B) (ρ x) (ρ h) (ρ u) (ρ v) := by
  simp only [terminal,Formula.rename,StructuralListSyntax.nilCode_rename,empty_rename]

theorem continuation_rename {m k} (w B h u v : Fin m) (ρ : Fin m → Fin k) :
    (continuation w B h u v).rename ρ = continuation (ρ w) (ρ B) (ρ h) (ρ u) (ρ v) := by
  simp only [continuation,Formula.neg,Formula.rename,empty_rename,PacketAffineSyntax.affine_rename,NaturalAdditionSyntax.sum_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem cell_rename {m k} (w B x h u v : Fin m) (ρ : Fin m → Fin k) :
    (cell w B x h u v).rename ρ = cell (ρ w) (ρ B) (ρ x) (ρ h) (ρ u) (ρ v) := by
  simp only [cell,Formula.rename,terminal_rename,continuation_rename]

theorem intro_continuation {m} {Γ : Context m} (w B h u v d : Fin m) (hu : Derives Γ (empty u).neg)
    (ha : Derives Γ (PacketAffineSyntax.affine w B d u v)) (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) :
    Derives Γ (continuation w B h u v) := by
  apply Derives.exI d
  exact of_eq (by simp only [Formula.instantiate,Formula.neg,Formula.rename,empty_rename,PacketAffineSyntax.affine_rename,NaturalAdditionSyntax.sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hu (.conjI ha hs))

end PPAC.Migration.Internal.PacketVarintCellSyntax
