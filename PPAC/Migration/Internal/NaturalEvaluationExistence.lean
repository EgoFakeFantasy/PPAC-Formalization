import PPAC.Migration.Internal.NaturalEvaluationSyntax

/-! 任意内部自然索引上的实际求值，显式消去后继域、原递归图和完整函数值见证。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationExistence
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem fiber_at {n m} {Γ : Context m} (q : Formula (n+3)) (τ : Fin n → Fin m) (d : Fin m)
    (ha : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique q τ)) (hd : Derives Γ (ordinal d)) :
    Derives Γ (OrdinalRecursionExistenceSyntax.fiber q τ d) := by
  have hi := Derives.allE d ha
  have hi' : Derives Γ ((ordinal d).imp (OrdinalRecursionExistenceSyntax.fiber q τ d)) := by
    simpa only [Formula.instantiate, Formula.rename, ordinal_rename, OrdinalRecursionExistenceSyntax.fiber_rename,
      paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hi' hd

theorem from_recursor {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r d f : Fin m)
    (ht : Derives Γ (trace p ρ w a r d f)) : Derives Γ (existsValue p ρ w a r) := by
  have hr := InsertLogic.new_member d r r (.conjL ht)
  have hy := Derives.impE (total_at f d r (.conjR (.conjL (.conjR ht)))) hr
  let Y := valueAt f.castSucc r.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have htY : Derives Ξ (trace p (paramsUp ρ) w.castSucc a.castSucc r.castSucc d.castSucc f.castSucc) := by
    simpa only [Formula.raise, trace_rename, paramsUp] using under ht Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have heval := intro_evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m) d.castSucc f.castSucc htY (.conjL hY)
  simpa only [Formula.raise, existsValue_rename, paramsUp] using intro_value p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m) heval

theorem at_natural {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w))
    (hord : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (ha : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a))) :
    Derives Γ (existsValue p ρ w a r) := by
  have hd := Derives.impE (step_at w r (.conjL hw)) hr
  let D := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) r.castSucc)
  let Γd := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hordD : Derives Γd (.all ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp (ordinal (Fin.last (m+1))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using under hord D
  have haD : Derives Γd (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp ρ) w.castSucc a.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using under ha D
  have hD : Derives Γd D := .hyp (Or.inl rfl)
  have hOrdD := OmegaOrdinals.at_member w.castSucc (Fin.last m) hordD (.conjL hD)
  have hf := fiber_at (matrix p) (extend (paramsUp ρ) w.castSucc a.castSucc) (Fin.last m) haD hOrdD
  let F := (OrdinalRecursionSyntax.recursor (matrix p) (extend (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc)
      (Fin.last (m+1)) (Fin.last m).castSucc).conj
    (OrdinalRecursionExistenceSyntax.uniqueAt (matrix p) (extend (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc)
      (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add F (Context.image Formula.raise Γd)
  simp only [OrdinalRecursionExistenceSyntax.fiber, extend_up] at hf
  change Derives Γd (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hsF : Derives Ξ (successor (Fin.last m).castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under (.conjR hD) F
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have ht : Derives Ξ (trace p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    .conjI hsF (.conjL hF)
  simpa only [Formula.raise, existsValue_rename, paramsUp] using from_recursor p (paramsUp (paramsUp ρ))
    w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) ht
end PPAC.Migration.Internal.NaturalEvaluationExistence
