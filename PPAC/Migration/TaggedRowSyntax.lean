import PPAC.Migration.ObjectGraphChoiceSelector

/-! 带标签行的纯对象语法：Row(r,x)精确表达r={〈x,y〉:y∈x}。 -/
namespace PPAC.Migration.TaggedRowSyntax
open Source SourceAlgebra SourceLogic PairSyntax

def entry {m} (x p : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) x.castSucc).conj (ordered p.castSucc x.castSucc (Fin.last m)))

def row {m} (r x : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) r.castSucc).iff (entry x.castSucc (Fin.last m)))

def rowExists {m} (x : Fin m) : Formula m := .ex (row (Fin.last m) x.castSucc)

def uniqueRow {m} (r x : Fin m) : Formula m := .all
  ((row (Fin.last m) x.castSucc).imp (.equal (Fin.last m) r.castSucc))

def rowFiber {m} (x : Fin m) : Formula m := .ex
  ((row (Fin.last m) x.castSucc).conj (uniqueRow (Fin.last m) x.castSucc))

def pairMatrix : Formula 3 := ordered 2 0 1

theorem entry_rename {m k} (x p : Fin m) (f : Fin m → Fin k) :
    (entry x p).rename f = entry (f x) (f p) := by
  simp only [entry, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem row_rename {m k} (r x : Fin m) (f : Fin m → Fin k) :
    (row r x).rename f = row (f r) (f x) := by
  simp only [row, Formula.rename, Formula.iff, entry_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rowExists_rename {m k} (x : Fin m) (f : Fin m → Fin k) :
    (rowExists x).rename f = rowExists (f x) := by
  simp only [rowExists, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueRow_rename {m k} (r x : Fin m) (f : Fin m → Fin k) :
    (uniqueRow r x).rename f = uniqueRow (f r) (f x) := by
  simp only [uniqueRow, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rowFiber_rename {m k} (x : Fin m) (f : Fin m → Fin k) :
    (rowFiber x).rename f = rowFiber (f x) := by
  simp only [rowFiber, Formula.rename, row_rename, uniqueRow_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pair_rel {m} (ρ : Fin 1 → Fin m) (y p : Fin m) :
    ReplacementPredicates.rel pairMatrix ρ y p = ordered p (ρ 0) y := by
  have h0 : Fin.lastCases p (Fin.lastCases y ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases p (Fin.lastCases y ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases p (Fin.lastCases y ρ) (1 : Fin 3) = y := by
    change Fin.lastCases p (Fin.lastCases y ρ) (Fin.last 1).castSucc = y
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h2 : Fin.lastCases p (Fin.lastCases y ρ) (2 : Fin 3) = p := by
    change Fin.lastCases p (Fin.lastCases y ρ) (Fin.last 2) = p
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, pairMatrix, ordered_rename, h0, h1, h2]

theorem pair_fiber {m} (ρ : Fin 1 → Fin m) (y : Fin m) :
    ReplacementPredicates.fiber pairMatrix ρ y = ObjectPairs.existsUnique (ρ 0) y := by
  simp only [ReplacementPredicates.fiber, ReplacementPredicates.unique, pair_rel,
    ObjectPairs.existsUnique, ObjectPairs.uniqueAt, ReplacementPredicates.paramsUp]

theorem pair_image {m} (x p : Fin m) :
    ReplacementPredicates.image pairMatrix (fun _ => x) x p = entry x p := by
  simp only [ReplacementPredicates.image, pair_rel, entry, ReplacementPredicates.paramsUp]

theorem pair_range {m} (x r : Fin m) :
    ReplacementPredicates.exactImage pairMatrix (fun _ => x) x r = row r x := by
  simp only [ReplacementPredicates.exactImage, pair_image, row]

theorem row_at {m} {Γ : Context m} (r x p : Fin m) (hr : Derives Γ (row r x)) :
    Derives Γ ((Formula.mem p r).iff (entry x p)) := by
  have hi := Derives.allE p hr
  simpa only [Formula.instantiate, Formula.rename, entry_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_entry {m} {Γ : Context m} (x p y : Fin m)
    (hy : Derives Γ (.mem y x)) (hp : Derives Γ (ordered p x y)) : Derives Γ (entry x p) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, ordered_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hy hp
end PPAC.Migration.TaggedRowSyntax
