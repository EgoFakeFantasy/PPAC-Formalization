import PPAC.Migration.Internal.ObjectSyntaxRenameIdentity

/-! 两幅完整实际索引图的纯对象复合关系；三个作用域均显式保留。 -/
namespace PPAC.Migration.Internal.SyntaxComposeSyntax
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax

def value {m} (r t i j : Fin m) : Formula m := .ex
  ((edge r.castSucc i.castSucc (Fin.last m)).conj (edge t.castSucc (Fin.last m) j.castSucc))

def matrix : Formula 4 := value 0 1 2 3

def composed {m} (w r t a c e g : Fin m) : Formula m :=
  (indexMap w r a c).conj ((indexMap w t c e).conj
    ((indexMap w g a e).conj (RelationGraphSyntax.edgeLaw matrix (Source.SetLanguage.args2 r t) a g)))

def existsGraph {m} (w r t a c e : Fin m) : Formula m := .ex
  (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m))

def graphFiber {m} (w r t a c e : Fin m) : Formula m := .ex
  ((composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)).conj
    (.all ((composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem value_rename {m k} (r t i j : Fin m) (ρ : Fin m → Fin k) :
    (value r t i j).rename ρ = value (ρ r) (ρ t) (ρ i) (ρ j) := by
  simp only [value, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

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

theorem composed_rename {m k} (w r t a c e g : Fin m) (ρ : Fin m → Fin k) :
    (composed w r t a c e g).rename ρ = composed (ρ w) (ρ r) (ρ t) (ρ a) (ρ c) (ρ e) (ρ g) := by
  simp only [composed, Formula.rename, indexMap_rename, RelationGraphSyntax.edgeLaw_rename]
  rfl

theorem existsGraph_rename {m k} (w r t a c e : Fin m) (ρ : Fin m → Fin k) :
    (existsGraph w r t a c e).rename ρ = existsGraph (ρ w) (ρ r) (ρ t) (ρ a) (ρ c) (ρ e) := by
  simp only [existsGraph, Formula.rename, composed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphFiber_rename {m k} (w r t a c e : Fin m) (ρ : Fin m → Fin k) :
    (graphFiber w r t a c e).rename ρ = graphFiber (ρ w) (ρ r) (ρ t) (ρ a) (ρ c) (ρ e) := by
  simp only [graphFiber, Formula.rename, composed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_value {m} {Γ : Context m} (r t i j k : Fin m)
    (hr : Derives Γ (edge r i k)) (ht : Derives Γ (edge t k j)) : Derives Γ (value r t i j) := by
  apply Derives.exI k
  simp only [Formula.instantiate, Formula.rename, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr ht
end PPAC.Migration.Internal.SyntaxComposeSyntax
