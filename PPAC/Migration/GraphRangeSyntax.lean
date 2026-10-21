import PPAC.Migration.ChoiceSyntax

/-! 完整内部函数图的精确实际值域；唯一输出纤维严格接原Replacement。 -/
namespace PPAC.Migration.GraphRangeSyntax
open Source SourceAlgebra SourceLogic GraphSyntax

def image {m} (f a y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (edge f.castSucc (Fin.last m) y.castSucc))

def range {m} (c f a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image f.castSucc a.castSucc (Fin.last m)))

def rangeExists {m} (f a : Fin m) : Formula m := .ex (range (Fin.last m) f.castSucc a.castSucc)

def matrix : Formula 3 := edge 0 1 2

theorem image_rename {m k} (f a y : Fin m) (r : Fin m → Fin k) :
    (image f a y).rename r = image (r f) (r a) (r y) := by
  simp only [image, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_rename {m k} (c f a : Fin m) (r : Fin m → Fin k) :
    (range c f a).rename r = range (r c) (r f) (r a) := by
  simp only [range, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rangeExists_rename {m k} (f a : Fin m) (r : Fin m → Fin k) :
    (rangeExists f a).rename r = rangeExists (r f) (r a) := by
  simp only [rangeExists, Formula.rename, range_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 1 → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel matrix ρ x y = edge (ρ 0) x y := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 3) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 1).castSucc = x
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h2 : Fin.lastCases y (Fin.lastCases x ρ) (2 : Fin 3) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 2) = y
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, edge_rename, h0, h1, h2]

theorem matrix_fiber {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    ReplacementPredicates.fiber matrix ρ x = valueExists (ρ 0) x := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel,
    valueExists, valueAt, ReplacementPredicates.paramsUp]

theorem matrix_image {m} (ρ : Fin 1 → Fin m) (a y : Fin m) :
    ReplacementPredicates.image matrix ρ a y = image (ρ 0) a y := by
  simp only [ReplacementPredicates.image, matrix_rel, image, ReplacementPredicates.paramsUp]

theorem matrix_range {m} (ρ : Fin 1 → Fin m) (a c : Fin m) :
    ReplacementPredicates.exactImage matrix ρ a c = range c (ρ 0) a := by
  simp only [ReplacementPredicates.exactImage, matrix_image, range, ReplacementPredicates.paramsUp]

theorem range_at {m} {Γ : Context m} (c f a y : Fin m) (hr : Derives Γ (range c f a)) :
    Derives Γ ((Formula.mem y c).iff (image f a y)) := by
  have hi := Derives.allE y hr
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_image {m} {Γ : Context m} (f a x y : Fin m)
    (hx : Derives Γ (.mem x a)) (he : Derives Γ (edge f x y)) : Derives Γ (image f a y) := by
  apply Derives.exI x
  simp only [Formula.instantiate, Formula.rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hx he
end PPAC.Migration.GraphRangeSyntax
