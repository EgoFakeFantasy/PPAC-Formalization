import PPAC.Migration.Internal.NaturalOrderBasic

/-! 差分见证显式限制在内部ω；唯一性也保留此范围。 -/
namespace PPAC.Migration.Internal.NaturalDifferenceSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open NaturalAdditionBounds (below below_rename)

def witness {m} (w a b d : Fin m) : Formula m := (Formula.mem d w).conj (sum w a d b)
def existsDifference {m} (w a b : Fin m) : Formula m := .ex (witness w.castSucc a.castSucc b.castSucc (Fin.last m))
def fiber {m} (w a b : Fin m) : Formula m := .ex
  ((witness w.castSucc a.castSucc b.castSucc (Fin.last m)).conj (.all
    ((witness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))
def positiveWitness {m} (w a b d : Fin m) : Formula m :=
  ((Formula.mem d w).conj (empty d).neg).conj (sum w a d b)
def positiveExists {m} (w a b : Fin m) : Formula m := .ex (positiveWitness w.castSucc a.castSucc b.castSucc (Fin.last m))
def property {m} (w a b : Fin m) : Formula m := (below a b).imp (existsDifference w a b)
def matrix : Formula 3 := property 0 1 2

theorem witness_rename {m k} (w a b d : Fin m) (r : Fin m → Fin k) :
    (witness w a b d).rename r = witness (r w) (r a) (r b) (r d) := by
  simp only [witness, Formula.rename, sum_rename]
theorem existsDifference_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (existsDifference w a b).rename r = existsDifference (r w) (r a) (r b) := by
  simp only [existsDifference, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (fiber w a b).rename r = fiber (r w) (r a) (r b) := by
  simp only [fiber, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem positiveWitness_rename {m k} (w a b d : Fin m) (r : Fin m → Fin k) :
    (positiveWitness w a b d).rename r = positiveWitness (r w) (r a) (r b) (r d) := by
  simp only [positiveWitness, Formula.rename, Formula.neg, empty_rename, sum_rename]
theorem positiveExists_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (positiveExists w a b).rename r = positiveExists (r w) (r a) (r b) := by
  simp only [positiveExists, Formula.rename, positiveWitness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem property_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (property w a b).rename r = property (r w) (r a) (r b) := by
  simp only [property, Formula.rename, below_rename, existsDifference_rename]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2]

theorem intro_difference {m} {Γ : Context m} (w a b d : Fin m) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (sum w a d b)) : Derives Γ (existsDifference w a b) := by
  have h : Derives Γ (witness w a b d) := .conjI hd hs
  apply Derives.exI d
  simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem intro_positive {m} {Γ : Context m} (w a b d : Fin m) (hd : Derives Γ (.mem d w))
    (hn : Derives Γ (empty d).neg) (hs : Derives Γ (sum w a d b)) : Derives Γ (positiveExists w a b) := by
  have h : Derives Γ (positiveWitness w a b d) := .conjI (.conjI hd hn) hs
  apply Derives.exI d
  simpa only [Formula.instantiate, positiveWitness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem target_subst {m} {Γ : Context m} (w a b c : Fin m) (he : Derives Γ (.equal b c))
    (hb : Derives Γ (existsDifference w a b)) : Derives Γ (existsDifference w a c) := by
  have hi : Derives Γ ((existsDifference w.castSucc a.castSucc (Fin.last m)).instantiate b) := by
    simpa only [Formula.instantiate, existsDifference_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb
  have ho := Derives.eqSubst (existsDifference w.castSucc a.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, existsDifference_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.NaturalDifferenceSyntax
