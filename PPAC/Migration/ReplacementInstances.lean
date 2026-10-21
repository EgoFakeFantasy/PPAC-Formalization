import PPAC.Migration.ExactImage
import PPAC.Migration.CollectionSyntax

/-! 将全Collection/Separation的闭实例接到精确像谓词；无额外推导核。 -/
namespace PPAC.Migration.ReplacementInstances
open Source SourceAlgebra ReplacementPredicates

def imageMatrix {n} (p : Formula (n+2)) : Formula (n+2) :=
  image p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))

theorem collection_core {n} (p : Formula (n+2)) : CollectionSyntax.core p =
    .all (collectionBody p Fin.castSucc (Fin.last n)) := rfl

theorem replacement_original {n} (p : Formula (n+2)) : Source.SetLanguage.replacement p =
    (Formula.all (replacementBody p Fin.castSucc (Fin.last n))).close := rfl

theorem separation_core {n} (p : Formula (n+2)) : SeparationSyntax.core (imageMatrix p) =
    .all (separationExists p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))) := by
  simp only [SeparationSyntax.core, imageMatrix, image_rename, SeparationSyntax.matrixIndex,
    Fin.lastCases_last, Fin.lastCases_castSucc, separationExists, separated]

theorem collection_instance {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m)
    (h : Derives Γ ((CollectionSyntax.collection p).rename Fin.elim0)) :
    Derives Γ (collectionBody p ρ a) := by
  have hc := specialize_close (CollectionSyntax.core p) ρ h
  rw [collection_core] at hc
  have hi := Derives.allE a hc
  simpa only [Formula.rename, Formula.instantiate, collectionBody_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem separation_instance {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w : Fin m)
    (h : Derives Γ ((Source.SetLanguage.separation (imageMatrix p)).rename Fin.elim0)) :
    Derives Γ (separationExists p ρ a w) := by
  rw [SeparationSyntax.source_core] at h
  have hs := specialize_close (SeparationSyntax.core (imageMatrix p)) (Fin.lastCases a ρ) h
  rw [separation_core] at hs
  have hi := Derives.allE w hs
  simpa only [Formula.rename, Formula.instantiate, separationExists_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.ReplacementInstances
