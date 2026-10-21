import PPAC.Migration.OrdinalRecursionExtension

/-! 实际后继递归图及保留旧前段的扩展结果；没有预设存在的字段。 -/
namespace PPAC.Migration.OrdinalRecursionSuccessorSyntax
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

def extension {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s f d : Fin m) : Formula m :=
  (OmegaSyntax.successor s d).conj ((ordinal s).conj ((recursor p ρ g s).conj (restrict f g d)))

def extensionExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) : Formula m := .ex (.ex
  (extension p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) (Fin.last m).castSucc f.castSucc.castSucc d.castSucc.castSucc))

def successorGraph {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) : Formula m := .ex
  ((OmegaSyntax.successor (Fin.last m) d.castSucc).conj (recursor p (paramsUp ρ) g.castSucc (Fin.last m)))

def successorExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  (successorGraph p (paramsUp ρ) d.castSucc (Fin.last m))

theorem extension_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s f d : Fin m) (r : Fin m → Fin k) :
    (extension p ρ g s f d).rename r = extension p (fun i => r (ρ i)) (r g) (r s) (r f) (r d) := by
  simp only [extension, Formula.rename, OmegaSyntax.successor_rename, ordinal_rename, recursor_rename, restrict_rename]

theorem extensionExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) (r : Fin m → Fin k) :
    (extensionExists p ρ f d).rename r = extensionExists p (fun i => r (ρ i)) (r f) (r d) := by
  simp only [extensionExists, Formula.rename, extension_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem successorGraph_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) (r : Fin m → Fin k) :
    (successorGraph p ρ d g).rename r = successorGraph p (fun i => r (ρ i)) (r d) (r g) := by
  simp only [successorGraph, Formula.rename, OmegaSyntax.successor_rename, recursor_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem successorExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (successorExists p ρ d).rename r = successorExists p (fun i => r (ρ i)) (r d) := by
  simp only [successorExists, Formula.rename, successorGraph_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_extension {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s f d : Fin m)
    (hx : Derives Γ (extension p ρ g s f d)) : Derives Γ (extensionExists p ρ f d) := by
  apply Derives.exI s
  apply Derives.exI g
  simpa only [Formula.instantiate, Formula.rename, extension_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx

theorem intro_successor {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g s : Fin m)
    (hs : Derives Γ (OmegaSyntax.successor s d)) (hg : Derives Γ (recursor p ρ g s)) : Derives Γ (successorGraph p ρ d g) := by
  apply Derives.exI s
  simpa only [Formula.instantiate, Formula.rename, OmegaSyntax.successor_rename, recursor_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs hg
end PPAC.Migration.OrdinalRecursionSuccessorSyntax
