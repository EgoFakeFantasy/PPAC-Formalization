import PPAC.Migration.GlobalMinimal

/-! 原Source.ordinal的严格纯对象展开；内部良序量化全部内部非空子集。 -/
namespace PPAC.Migration.OrdinalSyntax
open Source SourceAlgebra RestrictionSyntax

def transitiveSet {m} (a : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)) (Fin.last m).castSucc).imp (.mem (Fin.last (m+1)) a.castSucc.castSucc))))

def irreflexive {m} (a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (Formula.mem (Fin.last m) (Fin.last m)).neg)

def membershipTransitive {m} (a : Fin m) : Formula m := .all (.all (.all
  ((Formula.mem (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc).imp
      ((Formula.mem (Fin.last (m+2)) a.castSucc.castSucc.castSucc).imp
        (((Formula.mem (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
          (.mem (Fin.last (m+1)).castSucc (Fin.last (m+2)))).imp
            (.mem (Fin.last m).castSucc.castSucc (Fin.last (m+2)))))))))

def comparable {m} (a : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).imp
      ((Formula.equal (Fin.last m).castSucc (Fin.last (m+1))).disj
        ((Formula.mem (Fin.last m).castSucc (Fin.last (m+1))).disj (.mem (Fin.last (m+1)) (Fin.last m).castSucc))))))

def linear {m} (a : Fin m) : Formula m := (irreflexive a).conj ((membershipTransitive a).conj (comparable a))

def setMinimal {m} (c x : Fin m) : Formula m := (Formula.mem x c).conj
  (.all ((Formula.mem (Fin.last m) c.castSucc).imp (Formula.mem (Fin.last m) x.castSucc).neg))

def minimalExists {m} (c : Fin m) : Formula m := .ex (setMinimal c.castSucc (Fin.last m))

def wellFounded {m} (a : Fin m) : Formula m := .all
  (((subset (Fin.last m) a.castSucc).conj (MinimalPredicates.inhabited (Fin.last m))).imp (minimalExists (Fin.last m)))

def ordinal {m} (a : Fin m) : Formula m := (transitiveSet a).conj ((linear a).conj (wellFounded a))

theorem transitiveSet_original {m} (a : Fin m) : Source.SetLanguage.transitiveSet a = transitiveSet a := rfl

theorem linear_original {m} (a : Fin m) : Source.SetLanguage.membershipLinear a = linear a := rfl

theorem wellFounded_original {m} (a : Fin m) : Source.SetLanguage.membershipWellFounded a = wellFounded a := rfl

theorem ordinal_original {m} (a : Fin m) : Source.SetLanguage.ordinal a = ordinal a := rfl

theorem transitiveSet_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (transitiveSet a).rename ρ = transitiveSet (ρ a) := by
  simp only [transitiveSet, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem irreflexive_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (irreflexive a).rename ρ = irreflexive (ρ a) := by
  simp only [irreflexive, Formula.rename, Formula.neg, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem membershipTransitive_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (membershipTransitive a).rename ρ = membershipTransitive (ρ a) := by
  simp only [membershipTransitive, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem comparable_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (comparable a).rename ρ = comparable (ρ a) := by
  simp only [comparable, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem linear_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (linear a).rename ρ = linear (ρ a) := by
  simp only [linear, Formula.rename, irreflexive_rename, membershipTransitive_rename, comparable_rename]

theorem setMinimal_rename {m k} (c x : Fin m) (ρ : Fin m → Fin k) :
    (setMinimal c x).rename ρ = setMinimal (ρ c) (ρ x) := by
  simp only [setMinimal, Formula.rename, Formula.neg, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimalExists_rename {m k} (c : Fin m) (ρ : Fin m → Fin k) :
    (minimalExists c).rename ρ = minimalExists (ρ c) := by
  simp only [minimalExists, Formula.rename, setMinimal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem wellFounded_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (wellFounded a).rename ρ = wellFounded (ρ a) := by
  simp only [wellFounded, Formula.rename, subset_rename, MinimalPredicates.inhabited_rename, minimalExists_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem ordinal_rename {m k} (a : Fin m) (ρ : Fin m → Fin k) :
    (ordinal a).rename ρ = ordinal (ρ a) := by
  simp only [ordinal, Formula.rename, transitiveSet_rename, linear_rename, wellFounded_rename]

theorem transitiveSet_at {m} {Γ : Context m} (a x y : Fin m) (h : Derives Γ (transitiveSet a)) :
    Derives Γ ((Formula.mem x a).imp ((Formula.mem y x).imp (.mem y a))) := by
  have hi := Derives.allE y (Derives.allE x h)
  simpa only [Formula.instantiate, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem irreflexive_at {m} {Γ : Context m} (a x : Fin m) (h : Derives Γ (irreflexive a)) :
    Derives Γ ((Formula.mem x a).imp (Formula.mem x x).neg) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, Formula.neg, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem chain_at {m} {Γ : Context m} (a x y z : Fin m) (h : Derives Γ (membershipTransitive a)) :
    Derives Γ ((Formula.mem x a).imp ((Formula.mem y a).imp ((Formula.mem z a).imp
      (((Formula.mem x y).conj (.mem y z)).imp (.mem x z))))) := by
  have hi := Derives.allE z (Derives.allE y (Derives.allE x h))
  simpa only [Formula.instantiate, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem comparable_at {m} {Γ : Context m} (a x y : Fin m) (h : Derives Γ (comparable a)) :
    Derives Γ ((Formula.mem x a).imp ((Formula.mem y a).imp
      ((Formula.equal x y).disj ((Formula.mem x y).disj (.mem y x))))) := by
  have hi := Derives.allE y (Derives.allE x h)
  simpa only [Formula.instantiate, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem wellFounded_at {m} {Γ : Context m} (a c : Fin m) (h : Derives Γ (wellFounded a)) :
    Derives Γ (((subset c a).conj (MinimalPredicates.inhabited c)).imp (minimalExists c)) := by
  have hi := Derives.allE c h
  simpa only [Formula.instantiate, Formula.rename, subset_rename, MinimalPredicates.inhabited_rename, minimalExists_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.OrdinalSyntax
