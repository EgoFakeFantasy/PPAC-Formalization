import PPAC.Migration.ObjectRankCover

/-! 任意关系的最小见证秩：只收集唯一序数，不选择原关系的见证集合。 -/
namespace PPAC.Migration.WitnessRankSyntax
open Source SourceAlgebra SourceLogic OrdinalSyntax ReplacementPredicates

/-- 原关系参数ρ、输入x、候选秩a；实际y仍在对象存在量词内。 -/
def witness {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) : Formula m := .ex
  ((rel p (paramsUp ρ) x.castSucc (Fin.last m)).conj (LayerRankSyntax.rank (Fin.last m) a.castSucc))

def predicate {n} (p : Formula (n+2)) : Formula (n+2) :=
  witness p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))

def hasOrdinal {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m := .ex
  ((ordinal (Fin.last m)).conj (witness p (paramsUp ρ) x.castSucc (Fin.last m)))

def least {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) : Formula m :=
  OrdinalLeastSyntax.least (predicate p) (Fin.lastCases x ρ) a

def uniqueLeast {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) : Formula m := .all
  ((least p (paramsUp ρ) x.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiber {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m := .ex
  ((least p (paramsUp ρ) x.castSucc (Fin.last m)).conj (uniqueLeast p (paramsUp ρ) x.castSucc (Fin.last m)))

def matrix {n} (p : Formula (n+2)) : Formula (n+2) :=
  least p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))

def image {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d a : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) d.castSucc).conj (least p (paramsUp ρ) (Fin.last m) a.castSucc))

def range {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c d : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image p (paramsUp ρ) d.castSucc (Fin.last m)))

def rangeExists {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  (range p (paramsUp ρ) (Fin.last m) d.castSucc)

theorem append_rename {n m k} (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (fun i => r (Fin.lastCases x ρ i)) = Fin.lastCases (r x) (fun i => r (ρ i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

theorem append_up {n m} (ρ : Fin n → Fin m) (x : Fin m) :
    paramsUp (Fin.lastCases x ρ) = Fin.lastCases x.castSucc (paramsUp ρ) := append_rename ρ x Fin.castSucc

theorem witness_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) (r : Fin m → Fin k) :
    (witness p ρ x a).rename r = witness p (fun i => r (ρ i)) (r x) (r a) := by
  simp only [witness, Formula.rename, rel_rename, LayerRankSyntax.rank_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasOrdinal_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (hasOrdinal p ρ x).rename r = hasOrdinal p (fun i => r (ρ i)) (r x) := by
  simp only [hasOrdinal, Formula.rename, ordinal_rename, witness_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem least_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) (r : Fin m → Fin k) :
    (least p ρ x a).rename r = least p (fun i => r (ρ i)) (r x) (r a) := by
  simp only [least, OrdinalLeastSyntax.least_rename, append_rename]

theorem uniqueLeast_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) (r : Fin m → Fin k) :
    (uniqueLeast p ρ x a).rename r = uniqueLeast p (fun i => r (ρ i)) (r x) (r a) := by
  simp only [uniqueLeast, Formula.rename, least_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (fiber p ρ x).rename r = fiber p (fun i => r (ρ i)) (r x) := by
  simp only [fiber, Formula.rename, least_rename, uniqueLeast_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem image_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d a : Fin m) (r : Fin m → Fin k) :
    (image p ρ d a).rename r = image p (fun i => r (ρ i)) (r d) (r a) := by
  simp only [image, Formula.rename, least_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c d : Fin m) (r : Fin m → Fin k) :
    (range p ρ c d).rename r = range p (fun i => r (ρ i)) (r c) (r d) := by
  simp only [range, Formula.rename, Formula.iff, image_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rangeExists_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (rangeExists p ρ d).rename r = rangeExists p (fun i => r (ρ i)) (r d) := by
  simp only [rangeExists, Formula.rename, range_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem predicate_pred {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) :
    MinimalPredicates.pred (predicate p) (Fin.lastCases x ρ) a = witness p ρ x a := by
  simp only [MinimalPredicates.pred, predicate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem has_least {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) :
    OrdinalLeastSyntax.has (predicate p) (Fin.lastCases x ρ) = hasOrdinal p ρ x := by
  simp only [OrdinalLeastSyntax.has, OrdinalLeastSyntax.property, append_up, predicate_pred, hasOrdinal]

theorem least_fiber {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) :
    OrdinalLeastSyntax.fiber (predicate p) (Fin.lastCases x ρ) = fiber p ρ x := by
  simp only [OrdinalLeastSyntax.fiber, OrdinalLeastSyntax.uniqueLeast, append_up, fiber, uniqueLeast, least]

theorem least_property {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m)
    (hl : Derives Γ (least p ρ x a)) : Derives Γ ((ordinal a).conj (witness p ρ x a)) := by
  simpa only [OrdinalLeastSyntax.property, predicate_pred] using Derives.conjL hl

theorem matrix_rel {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) :
    ReplacementPredicates.rel (matrix p) ρ x a = least p ρ x a := by
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, least_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_unique {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m) :
    ReplacementPredicates.unique (matrix p) ρ x a = uniqueLeast p ρ x a := by
  simp only [ReplacementPredicates.unique, matrix_rel, uniqueLeast]

theorem matrix_fiber {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) :
    ReplacementPredicates.fiber (matrix p) ρ x = fiber p ρ x := by
  simp only [ReplacementPredicates.fiber, matrix_rel, matrix_unique, fiber]

theorem matrix_image {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d a : Fin m) :
    ReplacementPredicates.image (matrix p) ρ d a = image p ρ d a := by
  simp only [ReplacementPredicates.image, matrix_rel, image]

theorem matrix_range {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d c : Fin m) :
    ReplacementPredicates.exactImage (matrix p) ρ d c = range p ρ c d := by
  simp only [ReplacementPredicates.exactImage, matrix_image, range]

theorem range_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c d a : Fin m)
    (hr : Derives Γ (range p ρ c d)) : Derives Γ ((Formula.mem a c).iff (image p ρ d a)) := by
  have hi := Derives.allE a hr
  simpa only [Formula.instantiate, Formula.rename, image_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_witness {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a y : Fin m)
    (hy : Derives Γ (ReplacementPredicates.rel p ρ x y)) (hr : Derives Γ (LayerRankSyntax.rank y a)) :
    Derives Γ (witness p ρ x a) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, rel_rename, LayerRankSyntax.rank_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hy hr

theorem intro_hasOrdinal {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a : Fin m)
    (ha : Derives Γ (ordinal a)) (hw : Derives Γ (witness p ρ x a)) : Derives Γ (hasOrdinal p ρ x) := by
  apply Derives.exI a
  simp only [Formula.instantiate, Formula.rename, ordinal_rename, witness_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ha hw

theorem intro_image {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (d a x : Fin m)
    (hx : Derives Γ (.mem x d)) (hl : Derives Γ (least p ρ x a)) : Derives Γ (image p ρ d a) := by
  apply Derives.exI x
  simp only [Formula.instantiate, Formula.rename, least_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hx hl
end PPAC.Migration.WitnessRankSyntax
