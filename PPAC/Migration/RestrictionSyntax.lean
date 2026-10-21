import PPAC.Migration.GraphProperties
import PPAC.Migration.MinimalInstances

/-! 通过原完整Separation模式构造对象图限制；参数为任意内部集合。 -/
namespace PPAC.Migration.RestrictionSyntax
open Source SourceAlgebra PairSyntax GraphSyntax

def subset {m} (b d : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) b.castSucc).imp (.mem (Fin.last m) d.castSucc))

def restrict {m} (g f b : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) g.castSucc).iff
    ((Formula.mem (Fin.last m) f.castSucc).conj (entryOn b.castSucc (Fin.last m))))

def restrictExists {m} (f b : Fin m) : Formula m := .ex (restrict (Fin.last m) f.castSucc b.castSucc)

def edgeLaw {m} (g f b : Fin m) : Formula m :=
  .all (.all ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (.mem (Fin.last m).castSucc b.castSucc.castSucc))))

def witness {m} (g f b : Fin m) : Formula m :=
  (restrict g f b).conj ((functionOn g b).conj (edgeLaw g f b))

def existsRestriction {m} (f b : Fin m) : Formula m := .ex (witness (Fin.last m) f.castSucc b.castSucc)

def matrix : Formula 2 := entryOn 0 1

theorem subset_original {m} (b d : Fin m) : Source.SetLanguage.subset b d = subset b d := rfl

theorem subset_rename {m k} (b d : Fin m) (r : Fin m → Fin k) :
    (subset b d).rename r = subset (r b) (r d) := by
  simp only [subset, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem restrict_rename {m k} (g f b : Fin m) (r : Fin m → Fin k) :
    (restrict g f b).rename r = restrict (r g) (r f) (r b) := by
  simp only [restrict, Formula.iff, Formula.rename, entryOn_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem restrictExists_rename {m k} (f b : Fin m) (r : Fin m → Fin k) :
    (restrictExists f b).rename r = restrictExists (r f) (r b) := by
  simp only [restrictExists, Formula.rename, restrict_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem edgeLaw_rename {m k} (g f b : Fin m) (r : Fin m → Fin k) :
    (edgeLaw g f b).rename r = edgeLaw (r g) (r f) (r b) := by
  simp only [edgeLaw, Formula.iff, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m k} (g f b : Fin m) (r : Fin m → Fin k) :
    (witness g f b).rename r = witness (r g) (r f) (r b) := by
  simp only [witness, Formula.rename, restrict_rename, functionOn_rename, edgeLaw_rename]

theorem existsRestriction_rename {m k} (f b : Fin m) (r : Fin m → Fin k) :
    (existsRestriction f b).rename r = existsRestriction (r f) (r b) := by
  simp only [existsRestriction, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem subset_at {m} {Γ : Context m} (b d x : Fin m) (h : Derives Γ (subset b d)) :
    Derives Γ ((Formula.mem x b).imp (.mem x d)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem restrict_at {m} {Γ : Context m} (g f b p : Fin m) (h : Derives Γ (restrict g f b)) :
    Derives Γ ((Formula.mem p g).iff ((Formula.mem p f).conj (entryOn b p))) := by
  have hi := Derives.allE p h
  simpa only [Formula.instantiate, Formula.rename, entryOn_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (p : Fin m) :
    MinimalPredicates.pred matrix ρ p = entryOn (ρ 0) p := by
  have h0 : Fin.lastCases p ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases p ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases p ρ (1 : Fin 2) = p := by
    change Fin.lastCases p ρ (Fin.last 1) = p
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, entryOn_rename, h0, h1]

theorem exists_restrict {m} {Γ : Context m} (f b : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) :
    Derives Γ (restrictExists f b) := by
  have hi := MinimalInstances.separation_instance matrix (fun _ : Fin 1 => b) f hs
  simpa only [MinimalPredicates.separationExists, MinimalPredicates.separated, MinimalPredicates.satisfying,
    matrix_pred, restrictExists, restrict] using hi
end PPAC.Migration.RestrictionSyntax
