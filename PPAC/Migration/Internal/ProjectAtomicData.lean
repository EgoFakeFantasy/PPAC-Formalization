import PPAC.Migration.Internal.ProjectAtomicExistence

/-! Finite metadata against the pinned original Project encoder; not an internal compiler theorem. -/
namespace PPAC.Migration.Internal.ProjectAtomicData
open YesMetaZFC YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

def formula {depth : Nat} (kind : Fin 3) (x y : Project.Term depth) : Project.Formula 1 depth :=
  match kind.val with
  | 0 => .mem x y
  | 1 => Project.Formula.extensionalEq x y
  | _ => Project.Formula.subset x y

theorem source_encoding {depth : Nat} (kind : Fin 3) (x y : Project.Term depth) :
    ZFC.ProjectEncode.formula (formula kind x y) =
      NatPacket.Tree.node (ProjectAtomicSyntax.sourceTag kind) [ZFC.ProjectEncode.term x,ZFC.ProjectEncode.term y] := by
  rcases kind with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

end PPAC.Migration.Internal.ProjectAtomicData
