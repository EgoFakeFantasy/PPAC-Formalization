import PPAC.Migration.Internal.ProofTreeUniversalClosed

/-! 原12分支的实际递归前提改写为各自内部闭轨迹；完整arity与全部原守卫保持。 -/
namespace PPAC.Migration.Internal.ProofTreeTracedStep
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

def premise {m n} (test : Formula 1) (e : Expr n) (w : Fin m) (env : Fin n → Fin m) : Formula m := .ex
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m)))

def premises {m n} (test : Formula 1) : List (Expr n) → Fin m → (Fin n → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons e es, w, env => (premise test e w env).conj (premises test es w env)

def matrix {m} (test : Formula 1) (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) : Formula m :=
  (graph rule.head w env r).conj ((HornRuleSyntax.guards rule.guards w env).conj (premises test rule.premises w env))

def boundedMatrix {m} (test : Formula 1) (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) : Formula m :=
  (environmentNat rule.arity w env).conj ((HornExprBounds.environmentBound rule.arity r env).conj (matrix test rule w r env))

def body {m} (test : Formula 1) (rule : Rule) (w r : Fin m) : Formula (m+rule.arity) :=
  boundedMatrix test rule (old rule.arity w) (old rule.arity r) (slot rule.arity)

def application {m} (test : Formula 1) (rule : Rule) (w r : Fin m) : Formula m := existsMany rule.arity (body test rule w r)

def step {m} (test : Formula 1) : List Rule → Fin m → Fin m → Formula m
  | .nil, _, _ => .bot
  | .cons rule rules, w, r => (application test rule w r).disj (step test rules w r)

theorem premise_rename {m n l} (test : Formula 1) (e : Expr n) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin l) :
    (premise test e w env).rename ρ = premise test e (ρ w) (fun i => ρ (env i)) := by
  simp only [premise, Formula.rename, graph_rename, ProofTreeTraceSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem premises_rename {m n l} (test : Formula 1) (es : List (Expr n)) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin l) :
    (premises test es w env).rename ρ = premises test es (ρ w) (fun i => ρ (env i)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [premises, Formula.rename, premise_rename, ih]

theorem matrix_rename {m l} (test : Formula 1) (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) (ρ : Fin m → Fin l) :
    (matrix test rule w r env).rename ρ = matrix test rule (ρ w) (ρ r) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, graph_rename, HornRuleSyntax.guards_rename, premises_rename]

theorem boundedMatrix_rename {m l} (test : Formula 1) (rule : Rule) (w r : Fin m) (env : Fin rule.arity → Fin m) (ρ : Fin m → Fin l) :
    (boundedMatrix test rule w r env).rename ρ = boundedMatrix test rule (ρ w) (ρ r) (fun i => ρ (env i)) := by
  simp only [boundedMatrix, Formula.rename, environmentNat_rename, HornExprBounds.environmentBound_rename, matrix_rename]

theorem body_lift {m l} (test : Formula 1) (rule : Rule) (w r : Fin m) (ρ : Fin m → Fin l) :
    (body test rule w r).rename (lift rule.arity ρ) = body test rule (ρ w) (ρ r) := by
  simp only [body, boundedMatrix_rename, lift_old, lift_slot]

theorem application_rename {m l} (test : Formula 1) (rule : Rule) (w r : Fin m) (ρ : Fin m → Fin l) :
    (application test rule w r).rename ρ = application test rule (ρ w) (ρ r) := by
  simp only [application, existsMany_rename, body_lift]

theorem step_rename {m l} (test : Formula 1) (rules : List Rule) (w r : Fin m) (ρ : Fin m → Fin l) :
    (step test rules w r).rename ρ = step test rules (ρ w) (ρ r) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih => simp only [step, Formula.rename, application_rename, ih]

theorem premise_iff {m n} {Γ : Context m} (test : Formula 1) (e : Expr n) (w V : Fin m) (env : Fin n → Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((HornRuleSyntax.premise e w V env).iff (premise test e w env)) := by
  apply FormulaCodeCongruence.ex_congr
  have hv1 : Derives (Context.image Formula.raise Γ) (ProofTreeUniversalSyntax.value test w.castSucc V.castSucc) :=
    of_eq (ProofTreeUniversalSyntax.value_rename test w V Fin.castSucc) (.rename Fin.castSucc hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (ProofTreeUniversalValue.member_iff test _ _ _ hv1)

theorem premises_iff {m n} {Γ : Context m} (test : Formula 1) (es : List (Expr n)) (w V : Fin m) (env : Fin n → Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((HornRuleSyntax.premises es w V env).iff (premises test es w env)) := by
  induction es with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl _
  | cons e es ih => exact FormulaCodeCongruence.conj_congr (premise_iff test e w V env hv) ih

theorem matrix_iff {m} {Γ : Context m} (test : Formula 1) (rule : Rule) (w V r : Fin m) (env : Fin rule.arity → Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((HornRuleSyntax.matrix rule w r V env).iff (matrix test rule w r env)) :=
  FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (premises_iff test rule.premises w V env hv))

theorem application_iff {m} {Γ : Context m} (test : Formula 1) (rule : Rule) (w V r : Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((HornApplicationSyntax.application rule w r V).iff (application test rule w r)) := by
  apply HornApplicationBounds.existsMany_congr rule.arity
  have hvN := of_eq (ProofTreeUniversalSyntax.value_rename test w V (old rule.arity)) (HornBinderRules.under_many rule.arity hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (matrix_iff test rule (old rule.arity w) (old rule.arity V) (old rule.arity r) (slot rule.arity) hvN))

theorem step_iff {m} {Γ : Context m} (test : Formula 1) (rules : List Rule) (w V r : Fin m)
    (hv : Derives Γ (ProofTreeUniversalSyntax.value test w V)) :
    Derives Γ ((HornStepSyntax.step rules w r V).iff (step test rules w r)) := by
  induction rules with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl _
  | cons rule rules ih => exact SyntaxTypeLocalTransfer.disj_congr (application_iff test rule w V r hv) ih

end PPAC.Migration.Internal.ProofTreeTracedStep
