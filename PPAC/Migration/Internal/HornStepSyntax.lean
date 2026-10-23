import PPAC.Migration.Internal.HornApplicationRules

/-! 完整上游固定规则表逐原Rule编译为对象规则应用的析取。 -/
namespace PPAC.Migration.Internal.HornStepSyntax
open Source SourceAlgebra SourceLogic HornApplicationSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def step {m} : List Rule → Fin m → Fin m → Fin m → Formula m
  | .nil, _, _, _ => .bot
  | rule :: rules, w, row, trace => (application rule w row trace).disj (step rules w row trace)

def originalStep {m} (w row trace : Fin m) : Formula m := step YesMetaZFC.Automation.ObjectSyntaxTransform.rules w row trace

def lookupStep {m} (w row trace : Fin m) : Formula m :=
  (application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace).disj
    (application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace)

theorem step_rename {m k} (rules : List Rule) (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (step rules w row trace).rename ρ = step rules (ρ w) (ρ row) (ρ trace) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih => simp only [step, Formula.rename, application_rename, ih]

theorem originalStep_rename {m k} (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (originalStep w row trace).rename ρ = originalStep (ρ w) (ρ row) (ρ trace) := step_rename _ _ _ _ _

theorem lookupStep_rename {m k} (w row trace : Fin m) (ρ : Fin m → Fin k) :
    (lookupStep w row trace).rename ρ = lookupStep (ρ w) (ρ row) (ρ trace) := by
  simp only [lookupStep, Formula.rename, application_rename]

theorem rule_intro {m} {Γ : Context m} (rules : List Rule) (rule : Rule) (hr : rule ∈ rules) (w row trace : Fin m)
    (he : Derives Γ (application rule w row trace)) : Derives Γ (step rules w row trace) := by
  induction rules with
  | nil => simp only [List.not_mem_nil] at hr
  | cons a rules ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst rule
      exact .disjL he
    · exact .disjR (ih h)

theorem step_elim {m} {Γ : Context m} (rules : List Rule) (w row trace : Fin m) (p : Formula m)
    (he : Derives Γ (step rules w row trace))
    (hr : ∀ rule, rule ∈ rules → Derives Γ ((application rule w row trace).imp p)) : Derives Γ p := by
  induction rules generalizing Γ with
  | nil => exact .botE he
  | cons rule rules ih =>
    apply Derives.disjE he
    · exact .impE (add (hr rule List.mem_cons_self) _) (.hyp (Or.inl rfl))
    · exact ih (.hyp (Or.inl rfl)) (fun a ha => add (hr a (List.mem_cons_of_mem rule ha)) _)

end PPAC.Migration.Internal.HornStepSyntax
