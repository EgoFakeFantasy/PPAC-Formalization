import PPAC.Migration.Internal.HornUniversalTraceClosed
import PPAC.Migration.Internal.OriginalScalarPositive

/-! 原规则的全部真实前提可在同一实际内部轨迹集合中组合；不需要宿主轨迹选择。 -/
namespace PPAC.Migration.Internal.HornUniversalTraceRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

def tracedPremise {m n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) : Formula m := .ex
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m)))

def tracedPremises {m n} : List (Expr n) → Fin m → (Fin n → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons e es, w, env => (tracedPremise e w env).conj (tracedPremises es w env)

def tracedMatrix {m} (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) : Formula m :=
  (graph rule.head w env r).conj ((HornRuleSyntax.guards rule.guards w env).conj (tracedPremises rule.premises w env))

theorem tracedPremise_rename {m k n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (tracedPremise e w env).rename ρ = tracedPremise e (ρ w) (fun i => ρ (env i)) := by
  simp only [tracedPremise, Formula.rename, graph_rename, HornLookupConditionSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem tracedPremises_rename {m k n} (es : List (Expr n)) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (tracedPremises es w env).rename ρ = tracedPremises es (ρ w) (fun i => ρ (env i)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [tracedPremises, Formula.rename, tracedPremise_rename, ih]

theorem tracedMatrix_rename {m k} (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) (ρ : Fin m → Fin k) :
    (tracedMatrix rule w r env).rename ρ = tracedMatrix rule (ρ w) (ρ r) (fun i => ρ (env i)) := by
  simp only [tracedMatrix, Formula.rename, graph_rename, HornRuleSyntax.guards_rename, tracedPremises_rename]

theorem premise_iff {m n} {Γ : Context m} (e : Expr n) (w V : Fin m) (env : Fin n → Fin m)
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornRuleSyntax.premise e w V env).iff (tracedPremise e w env)) := by
  apply FormulaCodeCongruence.ex_congr
  have hv1 : Derives (Context.image Formula.raise Γ) (HornUniversalTraceSyntax.value w.castSucc V.castSucc) :=
    of_eq (HornUniversalTraceSyntax.value_rename w V Fin.castSucc) (.rename Fin.castSucc hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (HornUniversalTraceValue.member_iff _ _ _ hv1)

theorem premises_iff {m n} {Γ : Context m} (es : List (Expr n)) (w V : Fin m) (env : Fin n → Fin m)
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornRuleSyntax.premises es w V env).iff (tracedPremises es w env)) := by
  induction es with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl _
  | cons e es ih => exact FormulaCodeCongruence.conj_congr (premise_iff e w V env hv) ih

theorem matrix_iff {m} {Γ : Context m} (rule : Rule) (w V r : Fin m) (env : Fin rule.arity → Fin m)
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornRuleSyntax.matrix rule w r V env).iff (tracedMatrix rule w r env)) :=
  FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (premises_iff rule.premises w V env hv))

theorem intro_premise {m n} {Γ : Context m} (e : Expr n) (w y : Fin m) (env : Fin n → Fin m)
    (hg : Derives Γ (graph e w env y)) (ht : Derives Γ (HornLookupConditionSyntax.condition w y)) :
    Derives Γ (tracedPremise e w env) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, HornLookupConditionSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hg ht)

theorem apply_rule {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hm : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules)
    (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables) (w r : Fin m) (env : Fin rule.arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat rule.arity w env))
    (ht : Derives Γ (tracedMatrix rule w r env)) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat rule.arity w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename rule.arity w env Fin.castSucc) (under hn B)
  have ht1 : Derives Δ (tracedMatrix rule w.castSucc r.castSucc (fun i => (env i).castSucc)) := of_eq (tracedMatrix_rename rule w r env Fin.castSucc) (under ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hmatrix := Derives.impE (.conjR (matrix_iff rule w.castSucc (Fin.last m) r.castSucc (fun i => (env i).castSucc) hB)) ht1
  have hbound := OriginalScalarPositive.head_bound hZ1 rule hi w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL ht1)
  have happ := HornApplicationRules.intro_application rule w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) hn1 hbound hmatrix
  have hstep := HornStepSyntax.rule_intro _ rule hm w.castSucc r.castSucc (Fin.last m) happ
  have hr := HornExprRange.range hZ1 rule.head w.castSucc r.castSucc (fun i => (env i).castSucc) hw1 hn1 (.conjL ht1)
  exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm (HornUniversalTraceClosed.step_condition hZ1 _ _ _ hB hr hstep)

end PPAC.Migration.Internal.HornUniversalTraceRules
