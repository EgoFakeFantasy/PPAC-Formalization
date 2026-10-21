import PPAC.Migration.Internal.NaturalRecursion

/-! 递推末值由实际后继域及完整原递归图见证，不以宿主递归函数定义。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalRecursionSyntax

def trace {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r d f : Fin m) : Formula m :=
  (successor d r).conj (OrdinalRecursionSyntax.recursor (matrix p) (extend ρ w a) f d)
def witness {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m) : Formula (m+2) :=
  (trace p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (edge (Fin.last (m+1)) r.castSucc.castSucc y.castSucc.castSucc)
def evaluation {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m) : Formula m := .ex (.ex (witness p ρ w a r y))
def existsValue {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m) : Formula m := .ex
  (evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m))
def uniqueValue {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m) : Formula m := .ex
  ((evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m)).conj (.all
    ((evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem trace_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r d f : Fin m) (s : Fin m → Fin k) :
    (trace p ρ w a r d f).rename s = trace p (fun i => s (ρ i)) (s w) (s a) (s r) (s d) (s f) := by
  simp only [trace, Formula.rename, successor_rename, OrdinalRecursionSyntax.recursor_rename, extend_rename]
theorem witness_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m) (s : Fin m → Fin k) :
    (witness p ρ w a r y).rename (Formula.liftRen (Formula.liftRen s)) = witness p (fun i => s (ρ i)) (s w) (s a) (s r) (s y) := by
  simp only [witness, Formula.rename, trace_rename, edge_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem evaluation_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m) (s : Fin m → Fin k) :
    (evaluation p ρ w a r y).rename s = evaluation p (fun i => s (ρ i)) (s w) (s a) (s r) (s y) := by
  simp only [evaluation, Formula.rename, witness_rename]
theorem existsValue_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m) (s : Fin m → Fin k) :
    (existsValue p ρ w a r).rename s = existsValue p (fun i => s (ρ i)) (s w) (s a) (s r) := by
  simp only [existsValue, Formula.rename, evaluation_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem uniqueValue_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m) (s : Fin m → Fin k) :
    (uniqueValue p ρ w a r).rename s = uniqueValue p (fun i => s (ρ i)) (s w) (s a) (s r) := by
  simp only [uniqueValue, Formula.rename, evaluation_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_evaluation {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y d f : Fin m)
    (ht : Derives Γ (trace p ρ w a r d f)) (hy : Derives Γ (edge f r y)) : Derives Γ (evaluation p ρ w a r y) := by
  apply Derives.exI d
  apply Derives.exI f
  simp only [Formula.instantiate, witness, Formula.rename, trace_rename, edge_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hy

theorem intro_value {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m)
    (hy : Derives Γ (evaluation p ρ w a r y)) : Derives Γ (existsValue p ρ w a r) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, evaluation_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem eliminate_evaluation {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y : Fin m) (q : Formula m)
    (hy : Derives Γ (evaluation p ρ w a r y))
    (hc : Derives (Context.add (witness p ρ w a r y) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (witness p ρ w a r y))) at hy
  apply Derives.exE hy
  apply Derives.exE (p := witness p ρ w a r y) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.NaturalEvaluationSyntax
