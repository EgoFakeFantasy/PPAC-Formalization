import PPAC.Migration.ObjectOmega

/-! 对象ω的后继分解与传递性质；所有变量仍是内部集合。 -/
namespace PPAC.Migration.OmegaStructureSyntax
open Source SourceAlgebra OmegaSyntax RestrictionSyntax MinimalPredicates

def predecessor {m} (w x : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) w.castSucc).conj (successor x.castSucc (Fin.last m)))

def split {m} (w x : Fin m) : Formula m := (empty x).disj (predecessor w x)

def transitive {m} (x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) x.castSucc).imp (subset (Fin.last m) x.castSucc))

def splitMatrix : Formula 2 := split 0 1

def subsetMatrix : Formula 2 := subset 1 0

def transitiveMatrix : Formula 1 := transitive 0

theorem predecessor_rename {m k} (w x : Fin m) (r : Fin m → Fin k) :
    (predecessor w x).rename r = predecessor (r w) (r x) := by
  simp only [predecessor, Formula.rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem split_rename {m k} (w x : Fin m) (r : Fin m → Fin k) :
    (split w x).rename r = split (r w) (r x) := by
  simp only [split, Formula.rename, empty_rename, predecessor_rename]

theorem transitive_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (transitive x).rename r = transitive (r x) := by
  simp only [transitive, Formula.rename, subset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem split_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : pred splitMatrix ρ x = split (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [pred, splitMatrix, split_rename, h0, h1]

theorem subset_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : pred subsetMatrix ρ x = subset x (ρ 0) := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [pred, subsetMatrix, subset_rename, h0, h1]

theorem transitive_pred {m} (ρ : Fin 0 → Fin m) (x : Fin m) : pred transitiveMatrix ρ x = transitive x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 1) = x := by
    change Fin.lastCases x ρ (Fin.last 0) = x
    exact Fin.lastCases_last
  simp only [pred, transitiveMatrix, transitive_rename, h0]

theorem transitive_at {m} {Γ : Context m} (x y : Fin m) (h : Derives Γ (transitive x)) :
    Derives Γ ((Formula.mem y x).imp (subset y x)) := by
  have hi := Derives.allE y h
  simpa only [Formula.instantiate, Formula.rename, subset_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem holds_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w x : Fin m)
    (h : Derives Γ (OmegaInductionSyntax.holds p ρ w)) :
    Derives Γ ((Formula.mem x w).imp (pred p ρ x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, pred_rename, ReplacementPredicates.paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem predecessor_intro {m} {Γ : Context m} (w s x : Fin m)
    (hx : Derives Γ (.mem x w)) (hs : Derives Γ (successor s x)) : Derives Γ (predecessor w s) := by
  apply Derives.exI x
  simpa only [Formula.instantiate, Formula.rename, successor_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hx hs
end PPAC.Migration.OmegaStructureSyntax
