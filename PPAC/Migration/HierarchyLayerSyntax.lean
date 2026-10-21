import PPAC.Migration.HierarchyRecursion

/-! Vα为幂集并递归图在α处的实际值；域是α的实际后继，量词遍历全部内部集合。 -/
namespace PPAC.Migration.HierarchyLayerSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalRecursionSyntax

def graph {m} (f a : Fin m) : Formula m := recursor PowerUnionSyntax.matrix Fin.elim0 f a

def graphExists {m} (a : Fin m) : Formula m := .ex (graph (Fin.last m) a.castSucc)

def data {m} (s f a y : Fin m) : Formula m := (OmegaSyntax.successor s a).conj
  ((graph f s).conj (edge f a y))

def layer {m} (a y : Fin m) : Formula m := .ex (.ex
  (data (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc y.castSucc.castSucc))

def layerExists {m} (a : Fin m) : Formula m := .ex (layer a.castSucc (Fin.last m))

def uniqueLayer {m} (a y : Fin m) : Formula m := .all
  ((layer a.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def layerFiber {m} (a : Fin m) : Formula m := .ex
  ((layer a.castSucc (Fin.last m)).conj (uniqueLayer a.castSucc (Fin.last m)))

theorem empty_parameters {m} (ρ : Fin 0 → Fin m) : ρ = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem graph_rename {m k} (f a : Fin m) (r : Fin m → Fin k) :
    (graph f a).rename r = graph (r f) (r a) := by
  simp only [graph, recursor_rename, empty_parameters]

theorem graphExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (graphExists a).rename r = graphExists (r a) := by
  simp only [graphExists, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem data_rename {m k} (s f a y : Fin m) (r : Fin m → Fin k) :
    (data s f a y).rename r = data (r s) (r f) (r a) (r y) := by
  simp only [data, Formula.rename, OmegaSyntax.successor_rename, graph_rename, edge_rename]


theorem layer_rename {m k} (a y : Fin m) (r : Fin m → Fin k) :
    (layer a y).rename r = layer (r a) (r y) := by
  simp only [layer, Formula.rename, data_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem layerExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (layerExists a).rename r = layerExists (r a) := by
  simp only [layerExists, Formula.rename, layer_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem uniqueLayer_rename {m k} (a y : Fin m) (r : Fin m → Fin k) :
    (uniqueLayer a y).rename r = uniqueLayer (r a) (r y) := by
  simp only [uniqueLayer, Formula.rename, layer_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem layerFiber_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (layerFiber a).rename r = layerFiber (r a) := by
  simp only [layerFiber, Formula.rename, layer_rename, uniqueLayer_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_layer {m} {Γ : Context m} (s f a y : Fin m)
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hf : Derives Γ (graph f s)) (hy : Derives Γ (edge f a y)) : Derives Γ (layer a y) := by
  apply Derives.exI s
  apply Derives.exI f
  simp only [Formula.instantiate, data_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs (.conjI hf hy)

abbrev witnesses {m} (a y : Fin m) : Formula (m+2) :=
  data (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc y.castSucc.castSucc

theorem eliminate_layer {m} {Γ : Context m} (a y : Fin m) (q : Formula m)
    (hy : Derives Γ (layer a y))
    (hc : Derives (Context.add (witnesses a y) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (witnesses a y))) at hy
  apply Derives.exE hy
  apply Derives.exE (p := witnesses a y) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨t, ht, heq⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨t, Or.inr ht, heq⟩
end PPAC.Migration.HierarchyLayerSyntax
