import PPAC.Migration.LayerCoverSyntax

/-! 最小包含层索引是实际秩关系；唯一纤维和原Replacement矩阵精确对应。 -/
namespace PPAC.Migration.LayerRankSyntax
open Source SourceAlgebra SourceLogic LayerCoverSyntax

def rank {m} (x a : Fin m) : Formula m := OrdinalLeastSyntax.least containsMatrix (fun _ => x) a

def uniqueRank {m} (x a : Fin m) : Formula m := .all
  ((rank x.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiber {m} (x : Fin m) : Formula m := .ex
  ((rank x.castSucc (Fin.last m)).conj (uniqueRank x.castSucc (Fin.last m)))

def matrix : Formula 2 := rank 0 1

def image {m} (x a : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) x.castSucc).conj (rank (Fin.last m) a.castSucc))

def range {m} (c x : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image x.castSucc (Fin.last m)))

def rangeExists {m} (x : Fin m) : Formula m := .ex (range (Fin.last m) x.castSucc)

theorem rank_rename {m k} (x a : Fin m) (r : Fin m → Fin k) :
    (rank x a).rename r = rank (r x) (r a) := by
  simp only [rank, OrdinalLeastSyntax.least_rename]

theorem uniqueRank_rename {m k} (x a : Fin m) (r : Fin m → Fin k) :
    (uniqueRank x a).rename r = uniqueRank (r x) (r a) := by
  simp only [uniqueRank, Formula.rename, rank_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (fiber x).rename r = fiber (r x) := by
  simp only [fiber, Formula.rename, rank_rename, uniqueRank_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem image_rename {m k} (x a : Fin m) (r : Fin m → Fin k) :
    (image x a).rename r = image (r x) (r a) := by
  simp only [image, Formula.rename, rank_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_rename {m k} (c x : Fin m) (r : Fin m → Fin k) :
    (range c x).rename r = range (r c) (r x) := by
  simp only [range, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rangeExists_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (rangeExists x).rename r = rangeExists (r x) := by
  simp only [rangeExists, Formula.rename, range_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem least_fiber {m} (x : Fin m) :
    OrdinalLeastSyntax.fiber containsMatrix (fun _ => x) = fiber x := by
  simp only [OrdinalLeastSyntax.fiber, OrdinalLeastSyntax.uniqueLeast,
    rank, fiber, uniqueRank]

theorem rank_property {m} {Γ : Context m} (x a : Fin m) (hr : Derives Γ (rank x a)) : Derives Γ (atIndex x a) := by
  simpa only [contains_property] using Derives.conjL hr

theorem matrix_rel {m} (ρ : Fin 0 → Fin m) (x a : Fin m) :
    ReplacementPredicates.rel matrix ρ x a = rank x a := by
  have h0 : Fin.lastCases a (Fin.lastCases x ρ) (0 : Fin 2) = x := by
    change Fin.lastCases a (Fin.lastCases x ρ) (Fin.last 0).castSucc = x
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h1 : Fin.lastCases a (Fin.lastCases x ρ) (1 : Fin 2) = a := by
    change Fin.lastCases a (Fin.lastCases x ρ) (Fin.last 1) = a
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, rank_rename, h0, h1]

theorem matrix_fiber {m} (ρ : Fin 0 → Fin m) (x : Fin m) :
    ReplacementPredicates.fiber matrix ρ x = fiber x := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel, fiber, uniqueRank]

theorem matrix_image {m} (ρ : Fin 0 → Fin m) (x a : Fin m) :
    ReplacementPredicates.image matrix ρ x a = image x a := by
  simp only [ReplacementPredicates.image, matrix_rel, image]

theorem matrix_range {m} (ρ : Fin 0 → Fin m) (x c : Fin m) :
    ReplacementPredicates.exactImage matrix ρ x c = range c x := by
  simp only [ReplacementPredicates.exactImage, matrix_image, range]

theorem range_at {m} {Γ : Context m} (c x a : Fin m) (hr : Derives Γ (range c x)) :
    Derives Γ ((Formula.mem a c).iff (image x a)) := by
  have hi := Derives.allE a hr
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_image {m} {Γ : Context m} (x a y : Fin m)
    (hy : Derives Γ (.mem y x)) (hr : Derives Γ (rank y a)) : Derives Γ (image x a) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, rank_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hy hr
end PPAC.Migration.LayerRankSyntax
