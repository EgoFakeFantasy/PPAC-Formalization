import PPAC.Migration.HierarchyLimitMembership

/-! 实际早层的唯一纤维、原Replacement矩阵及精确像集合。 -/
namespace PPAC.Migration.HierarchyFamilySyntax
open Source SourceAlgebra SourceLogic HierarchyLayerSyntax

def image {m} (a v : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (layer (Fin.last m) v.castSucc))

def range {m} (c a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image a.castSucc (Fin.last m)))

def rangeExists {m} (a : Fin m) : Formula m := .ex (range (Fin.last m) a.castSucc)

def assembled {m} (a y : Fin m) : Formula m := .ex
  ((range (Fin.last m) a.castSucc).conj (InsertSyntax.unionOf y.castSucc (Fin.last m)))

def matrix : Formula 2 := layer 0 1

theorem image_rename {m k} (a v : Fin m) (r : Fin m → Fin k) :
    (image a v).rename r = image (r a) (r v) := by
  simp only [image, Formula.rename, layer_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_rename {m k} (c a : Fin m) (r : Fin m → Fin k) :
    (range c a).rename r = range (r c) (r a) := by
  simp only [range, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rangeExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (rangeExists a).rename r = rangeExists (r a) := by
  simp only [rangeExists, Formula.rename, range_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem assembled_rename {m k} (a y : Fin m) (r : Fin m → Fin k) :
    (assembled a y).rename r = assembled (r a) (r y) := by
  simp only [assembled, Formula.rename, range_rename, InsertSyntax.unionOf_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_image {m} {Γ : Context m} (a v b : Fin m)
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (layer b v)) : Derives Γ (image a v) := by
  apply Derives.exI b
  simp only [Formula.instantiate, Formula.rename, layer_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hb hv

theorem range_at {m} {Γ : Context m} (c a v : Fin m) (hr : Derives Γ (range c a)) :
    Derives Γ ((Formula.mem v c).iff (image a v)) := by
  have hi := Derives.allE v hr
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem matrix_rel {m} (ρ : Fin 0 → Fin m) (b v : Fin m) :
    ReplacementPredicates.rel matrix ρ b v = layer b v := by
  have h0 : Fin.lastCases v (Fin.lastCases b ρ) (0 : Fin 2) = b := by
    change Fin.lastCases v (Fin.lastCases b ρ) (Fin.last 0).castSucc = b
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h1 : Fin.lastCases v (Fin.lastCases b ρ) (1 : Fin 2) = v := by
    change Fin.lastCases v (Fin.lastCases b ρ) (Fin.last 1) = v
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, layer_rename, h0, h1]

theorem matrix_fiber {m} (ρ : Fin 0 → Fin m) (b : Fin m) :
    ReplacementPredicates.fiber matrix ρ b = layerFiber b := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel,
    layerFiber, uniqueLayer]

theorem matrix_image {m} (ρ : Fin 0 → Fin m) (a v : Fin m) :
    ReplacementPredicates.image matrix ρ a v = image a v := by
  simp only [ReplacementPredicates.image, matrix_rel, image]

theorem matrix_range {m} (ρ : Fin 0 → Fin m) (a c : Fin m) :
    ReplacementPredicates.exactImage matrix ρ a c = range c a := by
  simp only [ReplacementPredicates.exactImage, matrix_image, range]
end PPAC.Migration.HierarchyFamilySyntax
