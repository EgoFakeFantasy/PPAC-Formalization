import PPAC.Migration.PowerSetLogic

/-! 按完整历史图逐输入取得实际输出的幂集；原Replacement矩阵和精确值域。 -/
namespace PPAC.Migration.PowerValueSyntax
open Source SourceAlgebra SourceLogic GraphSyntax PowerSetSyntax
open ReplacementPredicates (paramsUp)

def value {m} (h b w : Fin m) : Formula m := .ex
  ((edge h.castSucc b.castSucc (Fin.last m)).conj (powerOf w.castSucc (Fin.last m)))

def valueExists {m} (h b : Fin m) : Formula m := .ex (value h.castSucc b.castSucc (Fin.last m))

def uniqueValue {m} (h b w : Fin m) : Formula m := .all
  ((value h.castSucc b.castSucc (Fin.last m)).imp (.equal (Fin.last m) w.castSucc))

def fiber {m} (h b : Fin m) : Formula m := .ex
  ((value h.castSucc b.castSucc (Fin.last m)).conj (uniqueValue h.castSucc b.castSucc (Fin.last m)))

def image {m} (a h w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (value h.castSucc (Fin.last m) w.castSucc))

def range {m} (c a h : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image a.castSucc h.castSucc (Fin.last m)))

def rangeExists {m} (a h : Fin m) : Formula m := .ex (range (Fin.last m) a.castSucc h.castSucc)

def matrix : Formula 3 := value 0 1 2

theorem value_rename {m k} (h b w : Fin m) (r : Fin m → Fin k) :
    (value h b w).rename r = value (r h) (r b) (r w) := by
  simp only [value, edge_rename, powerOf_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem valueExists_rename {m k} (h b : Fin m) (r : Fin m → Fin k) :
    (valueExists h b).rename r = valueExists (r h) (r b) := by
  simp only [valueExists, value_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem uniqueValue_rename {m k} (h b w : Fin m) (r : Fin m → Fin k) :
    (uniqueValue h b w).rename r = uniqueValue (r h) (r b) (r w) := by
  simp only [uniqueValue, value_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem fiber_rename {m k} (h b : Fin m) (r : Fin m → Fin k) :
    (fiber h b).rename r = fiber (r h) (r b) := by
  simp only [fiber, value_rename, uniqueValue_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem image_rename {m k} (a h w : Fin m) (r : Fin m → Fin k) :
    (image a h w).rename r = image (r a) (r h) (r w) := by
  simp only [image, value_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem range_rename {m k} (c a h : Fin m) (r : Fin m → Fin k) :
    (range c a h).rename r = range (r c) (r a) (r h) := by
  simp only [range, Formula.iff, image_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem rangeExists_rename {m k} (a h : Fin m) (r : Fin m → Fin k) :
    (rangeExists a h).rename r = rangeExists (r a) (r h) := by
  simp only [rangeExists, range_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_value {m} {Γ : Context m} (h b v w : Fin m)
    (he : Derives Γ (edge h b v)) (hp : Derives Γ (powerOf w v)) : Derives Γ (value h b w) := by
  apply Derives.exI v
  simpa only [Formula.instantiate, Formula.rename, edge_rename, powerOf_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI he hp

theorem range_at {m} {Γ : Context m} (c a h w : Fin m) (hr : Derives Γ (range c a h)) :
    Derives Γ ((Formula.mem w c).iff (image a h w)) := by
  have hi := Derives.allE w hr
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem matrix_rel {m} (ρ : Fin 1 → Fin m) (b w : Fin m) :
    ReplacementPredicates.rel matrix ρ b w = value (ρ 0) b w := by
  have h0 : Fin.lastCases w (Fin.lastCases b ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases w (Fin.lastCases b ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases w (Fin.lastCases b ρ) (1 : Fin 3) = b := by
    change Fin.lastCases w (Fin.lastCases b ρ) (Fin.last 1).castSucc = b
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h2 : Fin.lastCases w (Fin.lastCases b ρ) (2 : Fin 3) = w := by
    change Fin.lastCases w (Fin.lastCases b ρ) (Fin.last 2) = w
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, value_rename, h0, h1, h2]

theorem matrix_fiber {m} (ρ : Fin 1 → Fin m) (b : Fin m) :
    ReplacementPredicates.fiber matrix ρ b = fiber (ρ 0) b := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel, paramsUp, fiber, uniqueValue]

theorem matrix_image {m} (ρ : Fin 1 → Fin m) (a w : Fin m) :
    ReplacementPredicates.image matrix ρ a w = image a (ρ 0) w := by
  simp only [ReplacementPredicates.image, matrix_rel, paramsUp, image]

theorem matrix_range {m} (ρ : Fin 1 → Fin m) (a c : Fin m) :
    ReplacementPredicates.exactImage matrix ρ a c = range c a (ρ 0) := by
  simp only [ReplacementPredicates.exactImage, matrix_image, paramsUp, range]
end PPAC.Migration.PowerValueSyntax
