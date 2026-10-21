import PPAC.Migration.Internal.OmegaOrdinals
import PPAC.Migration.ObjectTransfiniteRecursion

/-! 自然前驱递推算子：全部参数是对象槽，无前驱时回到初值，不假定任意历史正确。 -/
namespace PPAC.Migration.Internal.NaturalRecursionSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates

def relationTotal {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) : Formula m := .all (.ex
  (rel p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))))
def relationFunctional {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) : Formula m := .all (.all (.all
  ((rel p (paramsUp (paramsUp (paramsUp ρ))) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
    ((rel p (paramsUp (paramsUp (paramsUp ρ))) (Fin.last m).castSucc.castSucc (Fin.last (m+2))).imp
      (.equal (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

def stepWitness {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m) : Formula (m+2) :=
  ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (successor x.castSucc.castSucc (Fin.last m).castSucc)).conj
    ((edge h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (rel p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) y.castSucc.castSucc))
def stepAt {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m) : Formula m := .ex (.ex (stepWitness p ρ w x h y))
def operation {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y : Fin m) : Formula m :=
  (stepAt p ρ w x h y).disj ((OmegaStructureSyntax.predecessor w x).neg.conj (.equal y a))
def hasOperation {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h : Fin m) : Formula m := .ex
  (operation p (paramsUp ρ) w.castSucc a.castSucc x.castSucc h.castSucc (Fin.last m))
def extend {n m} (ρ : Fin n → Fin m) (w a : Fin m) : Fin (n+2) → Fin m := Fin.lastCases a (Fin.lastCases w ρ)
def matrix {n} (p : Formula (n+2)) : Formula (n+5) := operation p
  (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
  (Fin.last n).castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc.castSucc
  (Fin.last (n+2)).castSucc.castSucc (Fin.last (n+3)).castSucc (Fin.last (n+4))

theorem relationTotal_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (relationTotal p ρ).rename r = relationTotal p (fun i => r (ρ i)) := by
  simp only [relationTotal, Formula.rename, rel_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem relationFunctional_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (relationFunctional p ρ).rename r = relationFunctional p (fun i => r (ρ i)) := by
  simp only [relationFunctional, Formula.rename, rel_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem stepWitness_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m) (r : Fin m → Fin k) :
    (stepWitness p ρ w x h y).rename (Formula.liftRen (Formula.liftRen r)) = stepWitness p (fun i => r (ρ i)) (r w) (r x) (r h) (r y) := by
  simp only [stepWitness, Formula.rename, successor_rename, edge_rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem stepAt_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m) (r : Fin m → Fin k) :
    (stepAt p ρ w x h y).rename r = stepAt p (fun i => r (ρ i)) (r w) (r x) (r h) (r y) := by
  simp only [stepAt, Formula.rename, stepWitness_rename]
theorem operation_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y : Fin m) (r : Fin m → Fin k) :
    (operation p ρ w a x h y).rename r = operation p (fun i => r (ρ i)) (r w) (r a) (r x) (r h) (r y) := by
  simp only [operation, Formula.rename, stepAt_rename, OmegaStructureSyntax.predecessor_rename, Formula.neg]
theorem hasOperation_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h : Fin m) (r : Fin m → Fin k) :
    (hasOperation p ρ w a x h).rename r = hasOperation p (fun i => r (ρ i)) (r w) (r a) (r x) (r h) := by
  simp only [hasOperation, Formula.rename, operation_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem extend_rename {n m k} (ρ : Fin n → Fin m) (w a : Fin m) (r : Fin m → Fin k) :
    (fun i => r (extend ρ w a i)) = extend (fun i => r (ρ i)) (r w) (r a) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extend, Fin.lastCases_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [extend, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem extend_up {n m} (ρ : Fin n → Fin m) (w a : Fin m) :
    paramsUp (extend ρ w a) = extend (paramsUp ρ) w.castSucc a.castSucc := extend_rename ρ w a Fin.castSucc

theorem matrix_operator {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y : Fin m) :
    OrdinalRecursionSyntax.operator (matrix p) (extend ρ w a) x h y = operation p ρ w a x h y := by
  simp only [OrdinalRecursionSyntax.operator, matrix, operation_rename, extend, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem total_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (u : Fin m)
    (ht : Derives Γ (relationTotal p ρ)) : Derives Γ (.ex (rel p (paramsUp ρ) u.castSucc (Fin.last m))) := by
  have hi := Derives.allE u ht
  simpa only [Formula.instantiate, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem functional_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (u y z : Fin m)
    (ht : Derives Γ (relationFunctional p ρ)) : Derives Γ ((rel p ρ u y).imp ((rel p ρ u z).imp (.equal y z))) := by
  have hi := Derives.allE z (Derives.allE y (Derives.allE u ht))
  simpa only [Formula.instantiate, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_step {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y t u : Fin m)
    (ht : Derives Γ (.mem t w)) (hs : Derives Γ (successor x t))
    (hu : Derives Γ (edge h t u)) (hr : Derives Γ (rel p ρ u y)) : Derives Γ (stepAt p ρ w x h y) := by
  apply Derives.exI t
  apply Derives.exI u
  simp only [Formula.instantiate, stepWitness, Formula.rename, successor_rename, edge_rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI ht hs) (.conjI hu hr)

theorem eliminate_step {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y : Fin m) (q : Formula m)
    (hs : Derives Γ (stepAt p ρ w x h y))
    (hc : Derives (Context.add (stepWitness p ρ w x h y) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (stepWitness p ρ w x h y))) at hs
  apply Derives.exE hs
  apply Derives.exE (p := stepWitness p ρ w x h y) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.NaturalRecursionSyntax
