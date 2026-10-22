import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! 原native头槽binder提升的纯关系：0→0，旧k→l提升为Succ(k)→Succ(l)。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax

def shiftBody {m} (r a i j : Fin m) : Formula (m+2) :=
  ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).conj
      ((successor i.castSucc.castSucc (Fin.last m).castSucc).conj
        (successor j.castSucc.castSucc (Fin.last (m+1))))

def shifted {m} (r a i j : Fin m) : Formula m := .ex (.ex (shiftBody r a i j))

def value {m} (r a i j : Fin m) : Formula m := ((empty i).conj (empty j)).disj (shifted r a i j)

def matrix : Formula 4 := value 0 1 2 3

def lifted {m} (w r a c u v g : Fin m) : Formula m :=
  (indexMap w r a c).conj ((successor u a).conj ((successor v c).conj
    ((indexMap w g u v).conj (RelationGraphSyntax.edgeLaw matrix (Source.SetLanguage.args2 r a) u g))))

def existsLift {m} (w r a c u v : Fin m) : Formula m := .ex
  (lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m))

def liftFiber {m} (w r a c u v : Fin m) : Formula m := .ex
  ((lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)).conj
    (.all ((lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem shifted_rename {m k} (r a i j : Fin m) (ρ : Fin m → Fin k) :
    (shifted r a i j).rename ρ = shifted (ρ r) (ρ a) (ρ i) (ρ j) := by
  simp only [shifted, shiftBody, Formula.rename, edge_rename, successor_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (r a i j : Fin m) (ρ : Fin m → Fin k) :
    (value r a i j).rename ρ = value (ρ r) (ρ a) (ρ i) (ρ j) := by
  simp only [value, Formula.rename, empty_rename, shifted_rename]

theorem matrix_rel {m} (ρ : Fin 2 → Fin m) (i j : Fin m) :
    rel matrix ρ i j = value (ρ 0) (ρ 1) i j := by
  have h0 : Fin.lastCases j (Fin.lastCases i ρ) (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases j (Fin.lastCases i ρ) ((0 : Fin 2).castSucc.castSucc) = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases j (Fin.lastCases i ρ) (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases j (Fin.lastCases i ρ) ((1 : Fin 2).castSucc.castSucc) = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases j (Fin.lastCases i ρ) (2 : Fin 4) = i := by
    change Fin.lastCases j (Fin.lastCases i ρ) (Fin.last 2).castSucc = i
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : Fin.lastCases j (Fin.lastCases i ρ) (3 : Fin 4) = j := by
    change Fin.lastCases j (Fin.lastCases i ρ) (Fin.last 3) = j
    exact Fin.lastCases_last
  simp only [rel, Source.SetLanguage.relation, matrix, value_rename, h0, h1, h2, h3]

theorem lifted_rename {m k} (w r a c u v g : Fin m) (ρ : Fin m → Fin k) :
    (lifted w r a c u v g).rename ρ = lifted (ρ w) (ρ r) (ρ a) (ρ c) (ρ u) (ρ v) (ρ g) := by
  simp only [lifted, Formula.rename, indexMap_rename, successor_rename, RelationGraphSyntax.edgeLaw_rename]
  rfl

theorem existsLift_rename {m k} (w r a c u v : Fin m) (ρ : Fin m → Fin k) :
    (existsLift w r a c u v).rename ρ = existsLift (ρ w) (ρ r) (ρ a) (ρ c) (ρ u) (ρ v) := by
  simp only [existsLift, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem liftFiber_rename {m k} (w r a c u v : Fin m) (ρ : Fin m → Fin k) :
    (liftFiber w r a c u v).rename ρ = liftFiber (ρ w) (ρ r) (ρ a) (ρ c) (ρ u) (ρ v) := by
  simp only [liftFiber, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_shifted {m} {Γ : Context m} (r a i j k l : Fin m)
    (hk : Derives Γ (.mem k a)) (he : Derives Γ (edge r k l))
    (hi : Derives Γ (successor i k)) (hj : Derives Γ (successor j l)) : Derives Γ (shifted r a i j) := by
  apply Derives.exI k
  apply Derives.exI l
  simp only [shiftBody, Formula.instantiate, Formula.rename, edge_rename, successor_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hk he) (.conjI hi hj)

theorem eliminate_shifted {m} {Γ : Context m} (r a i j : Fin m) (Q : Formula m)
    (he : Derives Γ (shifted r a i j))
    (hc : Derives (Context.add (shiftBody r a i j) (Context.image Formula.raise (Context.image Formula.raise Γ)))
      Q.raise.raise) : Derives Γ Q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨q, hq, hh⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨q, Or.inr hq, hh⟩
end PPAC.Migration.Internal.SyntaxIndexLiftSyntax
