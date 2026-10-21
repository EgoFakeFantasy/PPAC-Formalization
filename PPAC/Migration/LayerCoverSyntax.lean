import PPAC.Migration.HierarchyClosedInstances
import PPAC.Migration.ObjectOrdinalLeast

/-! 集合被实际层包含及属于某层的对象公式，覆盖全部内部集合。 -/
namespace PPAC.Migration.LayerCoverSyntax
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax

def contains {m} (x a : Fin m) : Formula m := .ex
  ((layer a.castSucc (Fin.last m)).conj (subset x.castSucc (Fin.last m)))

def atIndex {m} (x a : Fin m) : Formula m := (ordinal a).conj (contains x a)

def cover {m} (x : Fin m) : Formula m := .ex (atIndex x.castSucc (Fin.last m))

def memberCover {m} (x : Fin m) : Formula m := .ex (.ex
  ((ordinal (Fin.last m).castSucc).conj
    ((layer (Fin.last m).castSucc (Fin.last (m+1))).conj (.mem x.castSucc.castSucc (Fin.last (m+1))))))

def membersCovered {m} (x : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) x.castSucc).imp (cover (Fin.last m)))

def containsMatrix : Formula 2 := contains 0 1

def coverMatrix : Formula 1 := cover 0

theorem contains_rename {m k} (x a : Fin m) (r : Fin m → Fin k) :
    (contains x a).rename r = contains (r x) (r a) := by
  simp only [contains, Formula.rename, layer_rename, subset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem atIndex_rename {m k} (x a : Fin m) (r : Fin m → Fin k) :
    (atIndex x a).rename r = atIndex (r x) (r a) := by
  simp only [atIndex, Formula.rename, ordinal_rename, contains_rename]

theorem cover_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (cover x).rename r = cover (r x) := by
  simp only [cover, Formula.rename, atIndex_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem memberCover_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (memberCover x).rename r = memberCover (r x) := by
  simp only [memberCover, Formula.rename, ordinal_rename, layer_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem membersCovered_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (membersCovered x).rename r = membersCovered (r x) := by
  simp only [membersCovered, Formula.rename, cover_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem contains_pred {m} (x a : Fin m) :
    MinimalPredicates.pred containsMatrix (fun _ => x) a = contains x a := by
  have h0 : Fin.lastCases a (fun _ : Fin 1 => x) (0 : Fin 2) = x := by
    change Fin.lastCases a (fun _ : Fin 1 => x) (0 : Fin 1).castSucc = x
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases a (fun _ : Fin 1 => x) (1 : Fin 2) = a := by
    change Fin.lastCases a (fun _ : Fin 1 => x) (Fin.last 1) = a
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, containsMatrix, contains_rename, h0, h1]

theorem contains_property {m} (x a : Fin m) :
    OrdinalLeastSyntax.property containsMatrix (fun _ => x) a = atIndex x a := by
  simp only [OrdinalLeastSyntax.property, contains_pred, atIndex]

theorem contains_has {m} (x : Fin m) :
    OrdinalLeastSyntax.has containsMatrix (fun _ => x) = cover x := by
  simp only [OrdinalLeastSyntax.has, contains_property, cover]

theorem cover_pred {m} (ρ : Fin 0 → Fin m) (x : Fin m) : MinimalPredicates.pred coverMatrix ρ x = cover x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 1) = x := by
    change Fin.lastCases x ρ (Fin.last 0) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, coverMatrix, cover_rename, h0]

theorem members_below {m} (ρ : Fin 0 → Fin m) (x : Fin m) :
    SetInductionSyntax.below coverMatrix ρ x = membersCovered x := by
  simp only [SetInductionSyntax.below, cover_pred, membersCovered]

theorem members_at {m} {Γ : Context m} (x y : Fin m) (hh : Derives Γ (membersCovered x)) :
    Derives Γ ((Formula.mem y x).imp (cover y)) := by
  have hi := Derives.allE y hh
  simpa only [Formula.instantiate, Formula.rename, cover_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_contains {m} {Γ : Context m} (x a v : Fin m)
    (hl : Derives Γ (layer a v)) (hs : Derives Γ (subset x v)) : Derives Γ (contains x a) := by
  apply Derives.exI v
  simp only [Formula.instantiate, Formula.rename, layer_rename, subset_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hs

theorem intro_cover {m} {Γ : Context m} (x a v : Fin m)
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a v)) (hs : Derives Γ (subset x v)) : Derives Γ (cover x) := by
  apply Derives.exI a
  simp only [Formula.instantiate, atIndex_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ha (intro_contains x a v hl hs)

theorem intro_memberCover {m} {Γ : Context m} (x a v : Fin m)
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a v)) (hx : Derives Γ (.mem x v)) : Derives Γ (memberCover x) := by
  apply Derives.exI a
  apply Derives.exI v
  simp only [Formula.instantiate, Formula.rename, ordinal_rename, layer_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ha (.conjI hl hx)
end PPAC.Migration.LayerCoverSyntax
