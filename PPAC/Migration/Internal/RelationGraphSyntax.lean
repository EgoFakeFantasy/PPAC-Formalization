import PPAC.Migration.Internal.ObjectSyntaxRenameTerm

/-! 任意纯关系矩阵的原Kuratowski函数图合同；参数和全部候选均为对象变量。 -/
namespace PPAC.Migration.Internal.RelationGraphSyntax
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax ReplacementPredicates

def entry {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (x p : Fin m) : Formula m := .ex
  ((rel P (paramsUp ρ) x.castSucc (Fin.last m)).conj (ordered p.castSucc x.castSucc (Fin.last m)))

def entryMatrix {n} (P : Formula (n+2)) : Formula (n+2) :=
  entry P (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))

def pairImage {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d p : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) d.castSucc).conj (entry P (paramsUp ρ) (Fin.last m) p.castSucc))

def pairGraph {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) g.castSucc).iff (pairImage P (paramsUp ρ) d.castSucc (Fin.last m)))

def edgeLaw {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc d.castSucc.castSucc).conj
      (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))))))

def functionGraph {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : Formula m :=
  (functionOn g d).conj (edgeLaw P ρ d g)

def existsGraph {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  (functionGraph P (paramsUp ρ) d.castSucc (Fin.last m))

def graphFiber {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  ((functionGraph P (paramsUp ρ) d.castSucc (Fin.last m)).conj (.all
    ((functionGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem entry_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (x p : Fin m) (r : Fin m → Fin k) :
    (entry P ρ x p).rename r = entry P (fun i => r (ρ i)) (r x) (r p) := by
  simp only [entry, Formula.rename, rel_rename, ordered_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairImage_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d p : Fin m) (r : Fin m → Fin k) :
    (pairImage P ρ d p).rename r = pairImage P (fun i => r (ρ i)) (r d) (r p) := by
  simp only [pairImage, Formula.rename, entry_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairGraph_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) (r : Fin m → Fin k) :
    (pairGraph P ρ d g).rename r = pairGraph P (fun i => r (ρ i)) (r d) (r g) := by
  simp only [pairGraph, Formula.iff, Formula.rename, pairImage_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem edgeLaw_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) (r : Fin m → Fin k) :
    (edgeLaw P ρ d g).rename r = edgeLaw P (fun i => r (ρ i)) (r d) (r g) := by
  simp only [edgeLaw, Formula.iff, Formula.rename, edge_rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem functionGraph_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) (r : Fin m → Fin k) :
    (functionGraph P ρ d g).rename r = functionGraph P (fun i => r (ρ i)) (r d) (r g) := by
  simp only [functionGraph, Formula.rename, functionOn_rename, edgeLaw_rename]

theorem existsGraph_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (existsGraph P ρ d).rename r = existsGraph P (fun i => r (ρ i)) (r d) := by
  simp only [existsGraph, Formula.rename, functionGraph_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphFiber_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (graphFiber P ρ d).rename r = graphFiber P (fun i => r (ρ i)) (r d) := by
  simp only [graphFiber, Formula.rename, functionGraph_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem entryMatrix_rel {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (x p : Fin m) :
    rel (entryMatrix P) ρ x p = entry P ρ x p := by
  simp only [rel, Source.SetLanguage.relation, entryMatrix, entry_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem entryMatrix_graph {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) :
    exactImage (entryMatrix P) ρ d g = pairGraph P ρ d g := by
  simp only [exactImage, image, entryMatrix_rel, pairGraph, pairImage]

theorem intro_entry {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (x p y : Fin m)
    (hy : Derives Γ (rel P ρ x y)) (hp : Derives Γ (ordered p x y)) : Derives Γ (entry P ρ x p) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, rel_rename, ordered_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hy hp

theorem intro_image {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d p x : Fin m)
    (hx : Derives Γ (.mem x d)) (hp : Derives Γ (entry P ρ x p)) : Derives Γ (pairImage P ρ d p) := by
  apply Derives.exI x
  simp only [Formula.instantiate, Formula.rename, entry_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hx hp

theorem graph_at {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g p : Fin m)
    (hg : Derives Γ (pairGraph P ρ d g)) : Derives Γ ((Formula.mem p g).iff (pairImage P ρ d p)) := by
  simpa only [pairGraph, Formula.instantiate, Formula.iff, Formula.rename, pairImage_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE p hg

theorem law_at {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m)
    (hg : Derives Γ (edgeLaw P ρ d g)) : Derives Γ ((edge g x y).iff ((Formula.mem x d).conj (rel P ρ x y))) := by
  simpa only [edgeLaw, Formula.instantiate, Formula.iff, Formula.rename, edge_rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE x hg)

theorem relation_unique {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m)
    (ht : Derives Γ (total P ρ d)) (hx : Derives Γ (.mem x d))
    (hy : Derives Γ (rel P ρ x y)) (hz : Derives Γ (rel P ρ x z)) : Derives Γ (.equal y z) := by
  have hf := Derives.impE (specialize_total P ρ d x ht) hx
  let U := (rel P (paramsUp ρ) x.castSucc (Fin.last m)).conj (unique P (paramsUp ρ) x.castSucc (Fin.last m))
  let Δ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hf
  apply Derives.exE hf
  have hy1 : Derives Δ (rel P (paramsUp ρ) x.castSucc y.castSucc) := by simpa only [Formula.raise, rel_rename, paramsUp] using under hy U
  have hz1 : Derives Δ (rel P (paramsUp ρ) x.castSucc z.castSucc) := by simpa only [Formula.raise, rel_rename, paramsUp] using under hz U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hyu := Derives.impE (specialize_unique P _ _ _ _ (.conjR hU)) hy1
  have hzu := Derives.impE (specialize_unique P _ _ _ _ (.conjR hU)) hz1
  exact eq_trans hyu (eq_symm hzu)
end PPAC.Migration.Internal.RelationGraphSyntax
