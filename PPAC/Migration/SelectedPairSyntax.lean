import PPAC.Migration.TaggedFamilyLogic

/-! 选择集中的实际标签对及其精确像；不将原选择集假设为函数图。 -/
namespace PPAC.Migration.SelectedPairSyntax
open Source SourceAlgebra SourceLogic TaggedRowSyntax

def chosen {m} (s x p : Fin m) : Formula m := (Formula.mem p s).conj (entry x p)
def selected {m} (s x p : Fin m) : Formula m := (chosen s x p).conj (.all
  ((chosen s.castSucc x.castSucc (Fin.last m)).imp (.equal (Fin.last m) p.castSucc)))
def fiber {m} (s x : Fin m) : Formula m := .ex (selected s.castSucc x.castSucc (Fin.last m))
def image {m} (s a p : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (chosen s.castSucc (Fin.last m) p.castSucc))
def graph {m} (f s a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) f.castSucc).iff (image s.castSucc a.castSucc (Fin.last m)))
def graphExists {m} (s a : Fin m) : Formula m := .ex (graph (Fin.last m) s.castSucc a.castSucc)
def matrix : Formula 3 := chosen 0 1 2

theorem chosen_rename {m k} (s x p : Fin m) (r : Fin m → Fin k) :
    (chosen s x p).rename r = chosen (r s) (r x) (r p) := by
  simp only [chosen, Formula.rename, entry_rename]
theorem selected_rename {m k} (s x p : Fin m) (r : Fin m → Fin k) :
    (selected s x p).rename r = selected (r s) (r x) (r p) := by
  simp only [selected, Formula.rename, chosen_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (s x : Fin m) (r : Fin m → Fin k) :
    (fiber s x).rename r = fiber (r s) (r x) := by
  simp only [fiber, Formula.rename, selected_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem image_rename {m k} (s a p : Fin m) (r : Fin m → Fin k) :
    (image s a p).rename r = image (r s) (r a) (r p) := by
  simp only [image, Formula.rename, chosen_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem graph_rename {m k} (f s a : Fin m) (r : Fin m → Fin k) :
    (graph f s a).rename r = graph (r f) (r s) (r a) := by
  simp only [graph, Formula.rename, Formula.iff, image_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem graphExists_rename {m k} (s a : Fin m) (r : Fin m → Fin k) :
    (graphExists s a).rename r = graphExists (r s) (r a) := by
  simp only [graphExists, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 1 → Fin m) (x p : Fin m) :
    ReplacementPredicates.rel matrix ρ x p = chosen (ρ 0) x p := by
  have h0 : Fin.lastCases p (Fin.lastCases x ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases p (Fin.lastCases x ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases p (Fin.lastCases x ρ) (1 : Fin 3) = x := by
    change Fin.lastCases p (Fin.lastCases x ρ) (Fin.last 1).castSucc = x
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h2 : Fin.lastCases p (Fin.lastCases x ρ) (2 : Fin 3) = p := by
    change Fin.lastCases p (Fin.lastCases x ρ) (Fin.last 2) = p
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, chosen_rename, h0, h1, h2]
theorem matrix_fiber {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    ReplacementPredicates.fiber matrix ρ x = fiber (ρ 0) x := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel,
    fiber, selected, ReplacementPredicates.paramsUp]
theorem matrix_image {m} (ρ : Fin 1 → Fin m) (a p : Fin m) :
    ReplacementPredicates.image matrix ρ a p = image (ρ 0) a p := by
  simp only [ReplacementPredicates.image, matrix_rel, image, ReplacementPredicates.paramsUp]
theorem matrix_graph {m} (ρ : Fin 1 → Fin m) (a f : Fin m) :
    ReplacementPredicates.exactImage matrix ρ a f = graph f (ρ 0) a := by
  simp only [ReplacementPredicates.exactImage, matrix_image, graph, ReplacementPredicates.paramsUp]
theorem graph_at {m} {Γ : Context m} (f s a p : Fin m) (hg : Derives Γ (graph f s a)) :
    Derives Γ ((Formula.mem p f).iff (image s a p)) := by
  have hi := Derives.allE p hg
  simpa only [Formula.instantiate, Formula.rename, image_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem unique_at {m} {Γ : Context m} (s x p q : Fin m) (hp : Derives Γ (selected s x p)) :
    Derives Γ ((chosen s x q).imp (.equal q p)) := by
  have hi := Derives.allE q (.conjR hp)
  simpa only [Formula.instantiate, Formula.rename, chosen_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_image {m} {Γ : Context m} (s a x p : Fin m)
    (hx : Derives Γ (.mem x a)) (hp : Derives Γ (chosen s x p)) : Derives Γ (image s a p) := by
  apply Derives.exI x
  simp only [Formula.instantiate, Formula.rename, chosen_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hx hp
end PPAC.Migration.SelectedPairSyntax
