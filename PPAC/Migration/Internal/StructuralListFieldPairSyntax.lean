import PPAC.Migration.Internal.StructuralListFieldCons

/-! 原Kuratowski索引对与原Replacement精确像；图必须实际包含全部且仅有字段索引对。 -/
namespace PPAC.Migration.Internal.StructuralListFieldPairSyntax
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax StructuralListFieldSyntax

def entry {m} (w n i p : Fin m) : Formula m := .ex
  ((field w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (ordered p.castSucc i.castSucc (Fin.last m)))

def existsEntry {m} (w n i : Fin m) : Formula m := .ex (entry w.castSucc n.castSucc i.castSucc (Fin.last m))

def pairFiber {m} (w n i : Fin m) : Formula m := .ex
  ((entry w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (.all
    ((entry w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def matrix : Formula 4 := entry 0 1 2 3

def image {m} (w n l p : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) l.castSucc).conj (entry w.castSucc n.castSucc (Fin.last m) p.castSucc))

def graph {m} (w n l g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) g.castSucc).iff (image w.castSucc n.castSucc l.castSucc (Fin.last m)))

def existsGraph {m} (w n l : Fin m) : Formula m := .ex (graph w.castSucc n.castSucc l.castSucc (Fin.last m))

theorem entry_rename {m k} (w n i p : Fin m) (s : Fin m → Fin k) : (entry w n i p).rename s = entry (s w) (s n) (s i) (s p) := by
  simp only [entry, Formula.rename, field_rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsEntry_rename {m k} (w n i : Fin m) (s : Fin m → Fin k) : (existsEntry w n i).rename s = existsEntry (s w) (s n) (s i) := by
  simp only [existsEntry, Formula.rename, entry_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairFiber_rename {m k} (w n i : Fin m) (s : Fin m → Fin k) : (pairFiber w n i).rename s = pairFiber (s w) (s n) (s i) := by
  simp only [pairFiber, Formula.rename, entry_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem image_rename {m k} (w n l p : Fin m) (s : Fin m → Fin k) : (image w n l p).rename s = image (s w) (s n) (s l) (s p) := by
  simp only [image, Formula.rename, entry_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graph_rename {m k} (w n l g : Fin m) (s : Fin m → Fin k) : (graph w n l g).rename s = graph (s w) (s n) (s l) (s g) := by
  simp only [graph, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsGraph_rename {m k} (w n l : Fin m) (s : Fin m → Fin k) : (existsGraph w n l).rename s = existsGraph (s w) (s n) (s l) := by
  simp only [existsGraph, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 2 → Fin m) (i p : Fin m) : ReplacementPredicates.rel matrix ρ i p = entry (ρ 0) (ρ 1) i p := by
  have h0 : Fin.lastCases p (Fin.lastCases i ρ) (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases p (Fin.lastCases i ρ) (0 : Fin 2).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases p (Fin.lastCases i ρ) (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases p (Fin.lastCases i ρ) (1 : Fin 2).castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases p (Fin.lastCases i ρ) (2 : Fin 4) = i := by
    change Fin.lastCases p (Fin.lastCases i ρ) (Fin.last 2).castSucc = i
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : Fin.lastCases p (Fin.lastCases i ρ) (3 : Fin 4) = p := by
    change Fin.lastCases p (Fin.lastCases i ρ) (Fin.last 3) = p
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, entry_rename, h0, h1, h2, h3]

theorem matrix_fiber {m} (ρ : Fin 2 → Fin m) (i : Fin m) : ReplacementPredicates.fiber matrix ρ i = pairFiber (ρ 0) (ρ 1) i := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel, ReplacementPredicates.paramsUp, pairFiber]

theorem matrix_graph {m} (ρ : Fin 2 → Fin m) (l g : Fin m) : ReplacementPredicates.exactImage matrix ρ l g = graph (ρ 0) (ρ 1) l g := by
  simp only [ReplacementPredicates.exactImage, ReplacementPredicates.image, matrix_rel, ReplacementPredicates.paramsUp, graph, image]

theorem intro_entry {m} {Γ : Context m} (w n i p y : Fin m) (hf : Derives Γ (field w n i y))
    (hp : Derives Γ (ordered p i y)) : Derives Γ (entry w n i p) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, field_rename, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hf hp

theorem intro_existsEntry {m} {Γ : Context m} (w n i p : Fin m) (hp : Derives Γ (entry w n i p)) : Derives Γ (existsEntry w n i) := by
  apply Derives.exI p
  simpa only [Formula.instantiate, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp

theorem intro_image {m} {Γ : Context m} (w n l p i : Fin m) (hi : Derives Γ (.mem i l))
    (hp : Derives Γ (entry w n i p)) : Derives Γ (image w n l p) := by
  apply Derives.exI i
  simp only [Formula.instantiate, Formula.rename, entry_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hi hp

theorem graph_at {m} {Γ : Context m} (w n l g p : Fin m) (hg : Derives Γ (graph w n l g)) :
    Derives Γ ((Formula.mem p g).iff (image w n l p)) := by
  simpa only [graph, Formula.instantiate, Formula.rename, image_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE p hg
end PPAC.Migration.Internal.StructuralListFieldPairSyntax
