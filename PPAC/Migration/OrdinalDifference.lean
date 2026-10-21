import PPAC.Migration.ObjectOrdinalBasic

/-! 两集合的差性质和有界成员极小元；只用一个分离实例和Foundation。 -/
namespace PPAC.Migration.OrdinalDifference
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax

/-- 一个集合参数b，末变量x；正文精确为x∉b。 -/
def outsideMatrix : Formula 2 := (Formula.mem 1 0).neg

def difference {m} (a b x : Fin m) : Formula m :=
  (Formula.mem x a).conj (Formula.mem x b).neg

def hasDifference {m} (a b : Fin m) : Formula m :=
  .ex (difference a.castSucc b.castSucc (Fin.last m))

def minimal {m} (a b x : Fin m) : Formula m := (difference a b x).conj
  (.all ((difference a.castSucc b.castSucc (Fin.last m)).imp (Formula.mem (Fin.last m) x.castSucc).neg))

def minimalExists {m} (a b : Fin m) : Formula m :=
  .ex (minimal a.castSucc b.castSucc (Fin.last m))

theorem outside_pred {m} (b x : Fin m) :
    MinimalPredicates.pred outsideMatrix (fun _ => b) x = (Formula.mem x b).neg := rfl

theorem difference_rename {m k} (a b x : Fin m) (ρ : Fin m → Fin k) :
    (difference a b x).rename ρ = difference (ρ a) (ρ b) (ρ x) := rfl

theorem hasDifference_rename {m k} (a b : Fin m) (ρ : Fin m → Fin k) :
    (hasDifference a b).rename ρ = hasDifference (ρ a) (ρ b) := by
  simp only [hasDifference, Formula.rename, difference_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimal_rename {m k} (a b x : Fin m) (ρ : Fin m → Fin k) :
    (minimal a b x).rename ρ = minimal (ρ a) (ρ b) (ρ x) := by
  simp only [minimal, Formula.rename, Formula.neg, difference_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimalExists_rename {m k} (a b : Fin m) (ρ : Fin m → Fin k) :
    (minimalExists a b).rename ρ = minimalExists (ρ a) (ρ b) := by
  simp only [minimalExists, Formula.rename, minimal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimal_at {m} {Γ : Context m} (a b x y : Fin m) (h : Derives Γ (minimal a b x)) :
    Derives Γ ((difference a b y).imp (Formula.mem y x).neg) := by
  have hi := Derives.allE y (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, Formula.neg, difference_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem has_of_not_subset {m} {Γ : Context m} (a b : Fin m)
    (hn : Derives Γ (subset a b).neg) : Derives Γ (hasDifference a b) := by
  apply Derives.classical
  let Δ := Context.add (hasDifference a b).neg Γ
  have hno : Derives Δ (hasDifference a b).neg := .hyp (Or.inl rfl)
  have hs : Derives Δ (subset a b) := by
    apply Derives.allI
    have hno' : Derives (Context.image Formula.raise Δ) (hasDifference a.castSucc b.castSucc).neg := by
      simpa only [Formula.raise, Formula.neg, Formula.rename, hasDifference_rename] using Derives.rename Fin.castSucc hno
    apply Derives.impI
    apply Derives.classical
    let Ξ := Context.add (Formula.mem (Fin.last m) b.castSucc).neg
      (Context.add (.mem (Fin.last m) a.castSucc) (Context.image Formula.raise Δ))
    have hd : Derives Ξ (difference a.castSucc b.castSucc (Fin.last m)) :=
      .conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
    have he : Derives Ξ (hasDifference a.castSucc b.castSucc) := by
      apply Derives.exI (Fin.last m)
      simpa only [Formula.instantiate, difference_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
    exact .impE (add (add hno' _) _) he
  exact .impE (add hn _) hs

theorem exists_minimal {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hh : Derives Γ (hasDifference a b)) : Derives Γ (minimalExists a b) := by
  have hbounded : Derives Γ (MinimalPredicates.has outsideMatrix (fun _ => b) a) := by
    simpa only [MinimalPredicates.has, MinimalPredicates.satisfying, outside_pred,
      ReplacementPredicates.paramsUp, hasDifference, difference] using hh
  have hm := BoundedMinimal.minimal_exists outsideMatrix (fun _ => b) a hs hf hbounded
  exact hm

/-- a传递时，差性质的成员极小元的全部成员均属于b。 -/
theorem minimal_subset {m} {Γ : Context m} (a b x : Fin m)
    (ht : Derives Γ (transitiveSet a)) (hm : Derives Γ (minimal a b x)) : Derives Γ (subset x b) := by
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise Γ) (transitiveSet a.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc ht
  have hm' : Derives (Context.image Formula.raise Γ) (minimal a.castSucc b.castSucc x.castSucc) := by
    simpa only [Formula.raise, minimal_rename] using Derives.rename Fin.castSucc hm
  apply Derives.impI
  apply Derives.classical
  let Ξ := Context.add (Formula.mem (Fin.last m) b.castSucc).neg
    (Context.add (.mem (Fin.last m) x.castSucc) (Context.image Formula.raise Γ))
  have hx : Derives Ξ (.mem x.castSucc a.castSucc) := .conjL (.conjL (add (add hm' _) _))
  have hy : Derives Ξ (.mem (Fin.last m) x.castSucc) := .hyp (Or.inr (Or.inl rfl))
  have hya : Derives Ξ (.mem (Fin.last m) a.castSucc) :=
    .impE (.impE (add (add (transitiveSet_at a.castSucc x.castSucc (Fin.last m) ht') _) _) hx) hy
  have hd : Derives Ξ (difference a.castSucc b.castSucc (Fin.last m)) := .conjI hya (.hyp (Or.inl rfl))
  exact .impE (.impE (add (add (minimal_at a.castSucc b.castSucc x.castSucc (Fin.last m) hm') _) _) hd) hy
end PPAC.Migration.OrdinalDifference
