import PPAC.Migration.Internal.ArithmeticContext

/-! 步进关系的全值域界与初值的界，传到任意真实递推末值。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationRange
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def range {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (b : Fin m) : Formula m := .all (.all
  ((rel p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))).imp (.mem (Fin.last (m+1)) b.castSucc.castSucc)))

theorem range_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (b : Fin m) (r : Fin m → Fin k) :
    (range p ρ b).rename r = range p (fun i => r (ρ i)) (r b) := by
  simp only [range, Formula.rename, rel_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (b x y : Fin m)
    (hr : Derives Γ (range p ρ b)) : Derives Γ ((rel p ρ x y).imp (.mem y b)) := by
  have hi := Derives.allE y (Derives.allE x hr)
  simpa only [Formula.instantiate, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem operation_range {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y b : Fin m)
    (ha : Derives Γ (.mem a b)) (hr : Derives Γ (range p ρ b))
    (hy : Derives Γ (operation p ρ w a x h y)) : Derives Γ (.mem y b) := by
  apply Derives.disjE hy
  · let S := stepAt p ρ w x h y
    let W := stepWitness p ρ w x h y
    let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.add S Γ)))
    apply eliminate_step p ρ w x h y _ (Derives.hyp (Or.inl rfl))
    have hrW : Derives Ξ (range p (paramsUp (paramsUp ρ)) b.castSucc.castSucc) := by
      simpa only [Formula.raise, range_rename, paramsUp] using OrderedPairElimination.under_two (add hr S) W
    have hW : Derives Ξ W := .hyp (Or.inl rfl)
    exact .impE (range_at p (paramsUp (paramsUp ρ)) b.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hrW) (.conjR (.conjR hW))
  · exact mem_subst (eq_symm (.conjR (.hyp (Or.inl rfl)))) (add ha _)

theorem trace_range {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r d f y b : Fin m)
    (ha : Derives Γ (.mem a b)) (hr : Derives Γ (range p ρ b))
    (hf : Derives Γ (trace p ρ w a r d f)) (hy : Derives Γ (edge f r y)) : Derives Γ (.mem y b) := by
  have hrd := InsertLogic.new_member d r r (.conjL hf)
  have hh := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at (matrix p) (extend ρ w a) f d r y (.conjR (.conjR hf))) hrd) hy
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc r.castSucc).conj
    (OrdinalRecursionSyntax.operator (matrix p) (paramsUp (extend ρ w a)) r.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have haH : Derives Ξ (.mem a.castSucc b.castSucc) := under ha H
  have hrH : Derives Ξ (range p (paramsUp ρ) b.castSucc) := by
    simpa only [Formula.raise, range_rename, paramsUp] using under hr H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hop : Derives Ξ (operation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m) y.castSucc) := by
    simpa only [extend_up, matrix_operator] using Derives.conjR hH
  exact operation_range p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m) y.castSucc b.castSucc haH hrH hop

theorem evaluation_range {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r y b : Fin m)
    (ha : Derives Γ (.mem a b)) (hr : Derives Γ (range p ρ b))
    (hy : Derives Γ (evaluation p ρ w a r y)) : Derives Γ (.mem y b) := by
  let Y := witness p ρ w a r y
  let Ξ := Context.add Y (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_evaluation p ρ w a r y _ hy
  have haY : Derives Ξ (.mem a.castSucc.castSucc b.castSucc.castSucc) := OrderedPairElimination.under_two ha Y
  have hrY : Derives Ξ (range p (paramsUp (paramsUp ρ)) b.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename, paramsUp] using OrderedPairElimination.under_two hr Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  exact trace_range p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc b.castSucc.castSucc haY hrY (.conjL hY) (.conjR hY)
end PPAC.Migration.Internal.NaturalEvaluationRange
