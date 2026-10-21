import PPAC.Migration.IterationContext

/-! 每个内部长度的末值关系及Replacement矩阵，全部以实际有限轨迹定义。 -/
namespace PPAC.Migration.IterationValueSyntax
open Source SourceAlgebra SourceLogic GraphSyntax FiniteIterationSyntax

def value {m} (n z a r : Fin m) : Formula m := .ex (.ex
  ((witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc).conj
    (edge (Fin.last (m+1)) n.castSucc.castSucc r.castSucc.castSucc)))

def valueExists {m} (n z a : Fin m) : Formula m := .ex (value n.castSucc z.castSucc a.castSucc (Fin.last m))

def matrix : Formula 4 := value 2 0 1 3

theorem value_rename {m k} (n z a r : Fin m) (ρ : Fin m → Fin k) :
    (value n z a r).rename ρ = value (ρ n) (ρ z) (ρ a) (ρ r) := by
  simp only [value, Formula.rename, witness_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem valueExists_rename {m k} (n z a : Fin m) (ρ : Fin m → Fin k) :
    (valueExists n z a).rename ρ = valueExists (ρ n) (ρ z) (ρ a) := by
  simp only [valueExists, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_value {m} {Γ : Context m} (f d n z a r : Fin m)
    (hf : Derives Γ (witness f d n z a)) (hr : Derives Γ (edge f n r)) : Derives Γ (value n z a r) := by
  apply Derives.exI d
  apply Derives.exI f
  simpa only [Formula.instantiate, Formula.rename, witness_rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hf hr

def witnesses {m} (n z a r : Fin m) : Formula (m+2) :=
  (witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc).conj
    (edge (Fin.last (m+1)) n.castSucc.castSucc r.castSucc.castSucc)

theorem eliminate_value {m} {Γ : Context m} (n z a r : Fin m) (q : Formula m)
    (h : Derives Γ (value n z a r))
    (hc : Derives (Context.add (witnesses n z a r) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (witnesses n z a r))) at h
  apply Derives.exE h
  apply Derives.exE (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨t, ht, het⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨t, Or.inr ht, het⟩

theorem matrix_rel {m} (ρ : Fin 2 → Fin m) (n r : Fin m) :
    ReplacementPredicates.rel matrix ρ n r = value n (ρ 0) (ρ 1) r := by
  have h0 : Fin.lastCases r (Fin.lastCases n ρ) (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases r (Fin.lastCases n ρ) (0 : Fin 2).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases r (Fin.lastCases n ρ) (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases r (Fin.lastCases n ρ) (1 : Fin 2).castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases r (Fin.lastCases n ρ) (2 : Fin 4) = n := by
    change Fin.lastCases r (Fin.lastCases n ρ) (Fin.last 2).castSucc = n
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : Fin.lastCases r (Fin.lastCases n ρ) (3 : Fin 4) = r := by
    change Fin.lastCases r (Fin.lastCases n ρ) (Fin.last 3) = r
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, value_rename, h0, h1, h2, h3]

def uniqueValue {m} (n z a r : Fin m) : Formula m := .all
  ((value n.castSucc z.castSucc a.castSucc (Fin.last m)).imp (.equal (Fin.last m) r.castSucc))

def valueFiber {m} (n z a : Fin m) : Formula m := .ex
  ((value n.castSucc z.castSucc a.castSucc (Fin.last m)).conj (uniqueValue n.castSucc z.castSucc a.castSucc (Fin.last m)))

def imageValue {m} (w z a r : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (value (Fin.last m) z.castSucc a.castSucc r.castSucc))

def range {m} (c w z a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (imageValue w.castSucc z.castSucc a.castSucc (Fin.last m)))

theorem uniqueValue_rename {m k} (n z a r : Fin m) (ρ : Fin m → Fin k) :
    (uniqueValue n z a r).rename ρ = uniqueValue (ρ n) (ρ z) (ρ a) (ρ r) := by
  simp only [uniqueValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem valueFiber_rename {m k} (n z a : Fin m) (ρ : Fin m → Fin k) :
    (valueFiber n z a).rename ρ = valueFiber (ρ n) (ρ z) (ρ a) := by
  simp only [valueFiber, Formula.rename, value_rename, uniqueValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem imageValue_rename {m k} (w z a r : Fin m) (ρ : Fin m → Fin k) :
    (imageValue w z a r).rename ρ = imageValue (ρ w) (ρ z) (ρ a) (ρ r) := by
  simp only [imageValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_rename {m k} (c w z a : Fin m) (ρ : Fin m → Fin k) :
    (range c w z a).rename ρ = range (ρ c) (ρ w) (ρ z) (ρ a) := by
  simp only [range, Formula.iff, Formula.rename, imageValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_fiber {m} (ρ : Fin 2 → Fin m) (n : Fin m) :
    ReplacementPredicates.fiber matrix ρ n = valueFiber n (ρ 0) (ρ 1) := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel, ReplacementPredicates.paramsUp, valueFiber, uniqueValue]

theorem matrix_image {m} (ρ : Fin 2 → Fin m) (w r : Fin m) :
    ReplacementPredicates.image matrix ρ w r = imageValue w (ρ 0) (ρ 1) r := by
  simp only [ReplacementPredicates.image, matrix_rel, ReplacementPredicates.paramsUp, imageValue]

theorem matrix_range {m} (ρ : Fin 2 → Fin m) (w c : Fin m) :
    ReplacementPredicates.exactImage matrix ρ w c = range c w (ρ 0) (ρ 1) := by
  simp only [ReplacementPredicates.exactImage, matrix_image, ReplacementPredicates.paramsUp, range]
end PPAC.Migration.IterationValueSyntax
