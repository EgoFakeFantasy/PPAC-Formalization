import PPAC.Migration.Internal.SchemaIndexHead

/-! Exact interface to the original three BoundEmbedding maps; metadata only. -/
namespace PPAC.Migration.Internal.SchemaIndexSites
open YesMetaZFC YesMetaZFC.SetTheory
open SchemaIndexSyntax

def keptHeads (site : Fin 3) : Nat := if site.val = 0 then 1 else 2

def shiftAmount (site : Fin 3) : Nat := if site.val = 1 then 1 else 2

def sourceDepth (site : Fin 3) (n : Nat) : Nat := n + keptHeads site

def targetDepth (site : Fin 3) (n : Nat) : Nat := n + keptHeads site + shiftAmount site

def imageIndex (site : Fin 3) (i : Nat) : Nat := if i < keptHeads site then i else i + shiftAmount site

theorem separation_index {n : Nat} (i : Fin (n+1)) :
    (BoundEmbedding.unaryUnderTwo i).val = imageIndex 0 i.val := by
  refine Fin.cases rfl (fun j => ?_) i
  change j.val + 3 = if j.val + 1 < 1 then j.val + 1 else (j.val + 1) + 2
  split <;> omega

theorem collection_premise_index {n : Nat} (i : Fin (n+2)) :
    (BoundEmbedding.binaryUnderOne i).val = imageIndex 1 i.val := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  change k.val + 3 = if k.val + 2 < 2 then k.val + 2 else (k.val + 2) + 1
  split <;> omega

theorem collection_image_index {n : Nat} (i : Fin (n+2)) :
    (BoundEmbedding.binaryUnderTwo i).val = imageIndex 2 i.val := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  change k.val + 4 = if k.val + 2 < 2 then k.val + 2 else (k.val + 2) + 2
  split <;> omega

theorem scope_depths (site : Fin 3) (n : Nat) :
    sourceScope site (fun i : Fin 4 => n+i.val+1) = sourceDepth site n ∧
      targetScope site (fun i : Fin 4 => n+i.val+1) = targetDepth site n := by
  rcases site with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

end PPAC.Migration.Internal.SchemaIndexSites
