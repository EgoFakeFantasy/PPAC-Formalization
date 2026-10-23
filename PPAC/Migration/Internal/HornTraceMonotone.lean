import PPAC.Migration.Internal.HornLookupConditionSyntax

/-! 原Horn规则仅正向引用轨迹成员；增大内部轨迹保留每个真实规则应用。 -/
namespace PPAC.Migration.Internal.HornTraceMonotone
open Source SourceAlgebra SourceLogic HornRuleSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

theorem premise {m n} {Γ : Context m} (e : Expr n) (w R S : Fin m) (env : Fin n → Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornRuleSyntax.premise e w R env)) :
    Derives Γ (HornRuleSyntax.premise e w S env) := by
  let B := (HornExprSyntax.graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc S.castSucc) :=
    of_eq (RestrictionSyntax.subset_rename R S Fin.castSucc) (under hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, HornExprSyntax.graph_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.conjI (.conjL hB) (.impE (RestrictionSyntax.subset_at _ _ _ hs1) (.conjR hB)))

theorem premises {m n} {Γ : Context m} (es : List (Expr n)) (w R S : Fin m) (env : Fin n → Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornRuleSyntax.premises es w R env)) :
    Derives Γ (HornRuleSyntax.premises es w S env) := by
  induction es with
  | nil => exact truth_proved
  | cons e es ih => exact .conjI (premise e w R S env hs (.conjL he)) (ih (.conjR he))

theorem matrix {m} {Γ : Context m} (rule : Rule) (w r R S : Fin m) (env : Fin rule.arity → Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornRuleSyntax.matrix rule w r R env)) :
    Derives Γ (HornRuleSyntax.matrix rule w r S env) :=
  .conjI (.conjL he) (.conjI (.conjL (.conjR he)) (premises rule.premises w R S env hs (.conjR (.conjR he))))

theorem application {m} {Γ : Context m} (rule : Rule) (w r R S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornApplicationSyntax.application rule w r R)) :
    Derives Γ (HornApplicationSyntax.application rule w r S) := by
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ he
  have hs1 : Derives Δ (RestrictionSyntax.subset (old rule.arity R) (old rule.arity S)) :=
    of_eq (RestrictionSyntax.subset_rename R S (old rule.arity)) (HornBinderRules.under_body rule.arity hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := HornApplicationRules.intro_application rule (old rule.arity w) (old rule.arity r) (old rule.arity S) (slot rule.arity)
    (.conjL hB) (.conjL (.conjR hB)) (matrix rule _ _ _ _ _ hs1 (.conjR (.conjR hB)))
  exact of_eq (application_rename rule w r S (old rule.arity)).symm ho

theorem step {m} {Γ : Context m} (rules : List Rule) (w r R S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornStepSyntax.step rules w r R)) :
    Derives Γ (HornStepSyntax.step rules w r S) := by
  apply HornStepSyntax.step_elim rules w r R _ he
  intro rule hr
  apply Derives.impI
  exact HornStepSyntax.rule_intro rules rule hr w r S (application rule w r R S (add hs _) (.hyp (Or.inl rfl)))

theorem originalStep {m} {Γ : Context m} (w r R S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R S)) (he : Derives Γ (HornStepSyntax.originalStep w r R)) :
    Derives Γ (HornStepSyntax.originalStep w r S) := step _ w r R S hs he

theorem row_subst {m} {Γ : Context m} (w r s R : Fin m) (he : Derives Γ (.equal r s))
    (hr : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (HornStepSyntax.originalStep w s R) := by
  let P := HornStepSyntax.originalStep w.castSucc (Fin.last m) R.castSucc
  have h0 : P.instantiate r = HornStepSyntax.originalStep w r R := by
    simp only [P, Formula.instantiate, HornStepSyntax.originalStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate s = HornStepSyntax.originalStep w s R := by
    simp only [P, Formula.instantiate, HornStepSyntax.originalStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

end PPAC.Migration.Internal.HornTraceMonotone
