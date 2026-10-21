import PPAC.Migration.ObjectPairs

/-! 源PP/AC实际图公式的纯对象展开；functionOn同时排除杂项并保证完整定义域。 -/
namespace PPAC.Migration.GraphSyntax
open Source SourceAlgebra PairSyntax

def edge {m} (f x y : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc))

def hasEdge {m} (f x : Fin m) : Formula m := .ex (edge f.castSucc x.castSucc (Fin.last m))

def entryOn {m} (d p : Fin m) : Formula m :=
  .ex (.ex ((Formula.mem (Fin.last m).castSucc d.castSucc.castSucc).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def entriesOn {m} (f d : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) f.castSucc).imp (entryOn d.castSucc (Fin.last m)))

def valueAt {m} (f x y : Fin m) : Formula m :=
  (edge f x y).conj (.all ((edge f.castSucc x.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc)))

def valueExists {m} (f x : Fin m) : Formula m := .ex (valueAt f.castSucc x.castSucc (Fin.last m))

def totalOn {m} (f d : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) d.castSucc).imp (valueExists f.castSucc (Fin.last m)))

def functionOn {m} (f d : Fin m) : Formula m := (entriesOn f d).conj (totalOn f d)

theorem edge_original {m} (f x y : Fin m) : Source.SetLanguage.edge f x y = edge f x y := rfl

theorem edge_rename {m k} (f x y : Fin m) (r : Fin m → Fin k) :
    (edge f x y).rename r = edge (r f) (r x) (r y) := by
  simp only [edge, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasEdge_rename {m k} (f x : Fin m) (r : Fin m → Fin k) :
    (hasEdge f x).rename r = hasEdge (r f) (r x) := by
  simp only [hasEdge, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem entryOn_rename {m k} (d p : Fin m) (r : Fin m → Fin k) :
    (entryOn d p).rename r = entryOn (r d) (r p) := by
  simp only [entryOn, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem entriesOn_rename {m k} (f d : Fin m) (r : Fin m → Fin k) :
    (entriesOn f d).rename r = entriesOn (r f) (r d) := by
  simp only [entriesOn, Formula.rename, entryOn_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem valueAt_rename {m k} (f x y : Fin m) (r : Fin m → Fin k) :
    (valueAt f x y).rename r = valueAt (r f) (r x) (r y) := by
  simp only [valueAt, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem valueExists_rename {m k} (f x : Fin m) (r : Fin m → Fin k) :
    (valueExists f x).rename r = valueExists (r f) (r x) := by
  simp only [valueExists, Formula.rename, valueAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem totalOn_rename {m k} (f d : Fin m) (r : Fin m → Fin k) :
    (totalOn f d).rename r = totalOn (r f) (r d) := by
  simp only [totalOn, Formula.rename, valueExists_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem functionOn_rename {m k} (f d : Fin m) (r : Fin m → Fin k) :
    (functionOn f d).rename r = functionOn (r f) (r d) := by
  simp only [functionOn, Formula.rename, entriesOn_rename, totalOn_rename]

theorem entries_at {m} {Γ : Context m} (f d p : Fin m) (h : Derives Γ (entriesOn f d)) :
    Derives Γ ((Formula.mem p f).imp (entryOn d p)) := by
  have hi := Derives.allE p h
  simpa only [Formula.instantiate, Formula.rename, entryOn_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem total_at {m} {Γ : Context m} (f d x : Fin m) (h : Derives Γ (totalOn f d)) :
    Derives Γ ((Formula.mem x d).imp (valueExists f x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, valueExists_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem unique_at {m} {Γ : Context m} (f x y z : Fin m) (h : Derives Γ (valueAt f x y)) :
    Derives Γ ((edge f x z).imp (.equal z y)) := by
  have hi := Derives.allE z (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
theorem functionOn_original {m} (f d : Fin m) : Source.SetLanguage.functionOn f d = functionOn f d := by
  simp only [Source.SetLanguage.functionOn, edge_original, ordered_original]
  change (functionOn (0 : Fin 2) 1).rename (Source.SetLanguage.args2 f d) = _
  rw [functionOn_rename, args2_first, args2_second]
end PPAC.Migration.GraphSyntax
