import PPAC.Migration.IterationRangeClosed

/-! 包含任意集合全部成员的传递覆盖，不预设秩或宿主良基性。 -/
namespace PPAC.Migration.TransitiveCoverSyntax
open Source SourceAlgebra OmegaStructureSyntax RestrictionSyntax

def cover {m} (b a : Fin m) : Formula m := (subset a b).conj (transitive b)

def coverExists {m} (a : Fin m) : Formula m := .ex (cover (Fin.last m) a.castSucc)

theorem cover_rename {m k} (b a : Fin m) (ρ : Fin m → Fin k) :
    (cover b a).rename ρ = cover (ρ b) (ρ a) := by
  simp only [cover, Formula.rename, subset_rename, transitive_rename]

theorem coverExists_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (coverExists a).rename ρ = coverExists (ρ a) := by
  simp only [coverExists, Formula.rename, cover_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.TransitiveCoverSyntax
