import PPAC.Migration.Internal.OriginalRuleHeadVariables
import PPAC.Migration.Internal.OriginalArgumentsDispatch

/-! 原nil/cons的实际存在赋值与原前提轨迹引入；两个任意内部子轨迹可组合。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsTraceRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform

def headPremise : Expr 7 := row 1 (.var 0) (.var 1) (.var 2) (.var 3) (.var 5)

def tailPremise : Expr 7 := row 2 (.var 0) (.var 1) (.var 2) (.var 4) (.var 6)

theorem actual_cons_premises : consArguments.premises = [headPremise, tailPremise] := rfl

theorem nil_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph nilArguments.head w env r))
    (hg : Derives Γ (HornRuleSyntax.guards nilArguments.guards w env)) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalRuleHeadVariables.apply_original_rule hZ nilArguments (by simp [rules]) w r env hw hn
    (.conjI hh (.conjI hg HornRuleSyntax.truth_proved))

theorem cons_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hh : Derives Γ (graph consArguments.head w env r))
    (hp : Derives Γ (tracedPremise headPremise w env))
    (ht : Derives Γ (tracedPremise tailPremise w env)) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalRuleHeadVariables.apply_original_rule hZ consArguments (by simp [rules]) w r env hw hn
    (.conjI hh (.conjI HornRuleSyntax.truth_proved (.conjI hp (.conjI ht HornRuleSyntax.truth_proved))))

theorem cons_conditions_at_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r first rest : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hh : Derives Γ (graph consArguments.head w env r))
    (hfirst : Derives Γ (graph headPremise w env first)) (hrest : Derives Γ (graph tailPremise w env rest))
    (hpf : Derives Γ (HornLookupConditionSyntax.condition w first)) (hpt : Derives Γ (HornLookupConditionSyntax.condition w rest)) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  cons_condition hZ w r env hw hn hh (intro_premise headPremise w first env hfirst hpf) (intro_premise tailPremise w rest env hrest hpt)

end PPAC.Migration.Internal.OriginalArgumentsTraceRules
