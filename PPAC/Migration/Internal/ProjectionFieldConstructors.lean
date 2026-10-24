import PPAC.Migration.Internal.ProjectionGetInduction
import PPAC.Migration.Internal.RawCodeField

/-! 原field两条规则的真实父查询构造，正码只要求实际get子查询。 -/
namespace PPAC.Migration.Internal.ProjectionFieldConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d Fin.elim0)))
def positiveFields : Fin 3 → Expr 4 := ProjectionTracePremises.three (ObjectProjection.raw (.var 0) (.var 1)) (.var 2) (.var 3)
def positivePremise : Expr 4 := Expr.node (.literal 1) (List.ofFn (ProjectionTracePremises.getFields 1 2 3))

theorem zero_head : ObjectProjection.fieldZero.head = Expr.node (.literal 2) (List.ofFn ProjectionGetConstructors.zeroFields) := rfl
theorem positive_head : ObjectProjection.fieldPositive.head = Expr.node (.literal 2) (List.ofFn positiveFields) := rfl
theorem positive_premises : ObjectProjection.fieldPositive.premises = [positivePremise] := rfl

theorem zero_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hx : Derives Γ (empty x)) (hy : Derives Γ (empty y)) :
    Derives Γ (ProjectionTraceSyntax.field w x i y) := by
  let env : Fin 1 → Fin m := fun _ => i
  have hn : Derives Γ (environmentNat 1 w env) := HornApplicationRules.intro_nat w env (fun _ => hi)
  have h0 : Derives Γ (graph (ProjectionGetConstructors.zeroFields 0) w env x) := hx
  have h1 : Derives Γ (graph (ProjectionGetConstructors.zeroFields 1) w env i) := .conjI hi (.eqRefl _)
  have h2 : Derives Γ (graph (ProjectionGetConstructors.zeroFields 2) w env y) := hy
  have hs : ∀ j, Derives Γ (graph (ProjectionGetConstructors.zeroFields j) w env (SyntaxAtomSyntax.three x i y j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun z => Fin.elim0 z)))
  have hq := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.fieldZero (by simp [ObjectProjection.rules]) w env hw hn HornRuleSyntax.truth_proved
  have he := ProjectionExprQuery.constructor_query_iff hZ 3 2 ProjectionGetConstructors.zeroFields w env (SyntaxAtomSyntax.three x i y) hw hn hs
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) zero_head) hq)

theorem positive_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag p x i y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem p w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x)) (hq : Derives Γ (ProjectionTraceSyntax.get w p i y)) :
    Derives Γ (ProjectionTraceSyntax.field w x i y) := by
  have hi := ProjectionNodeFields.get_natural_at hZ w p i y 1 hw hq
  have hy := ProjectionNodeFields.get_natural_at hZ w p i y 2 hw hq
  let env := four tag p i y
  have hn : Derives Γ (environmentNat 4 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases ht (Fin.cases hp (Fin.cases hi (Fin.cases hy (fun z => Fin.elim0 z)))))
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have h0 : Derives Γ (graph (positiveFields 0) w env x) := HornExprStructural.raw_graph (.var 0) (.var 1) w tag p x env (hv 0) (hv 1) hr
  have h1 : Derives Γ (graph (positiveFields 1) w env i) := hv 2
  have h2 : Derives Γ (graph (positiveFields 2) w env y) := hv 3
  have hs : ∀ j, Derives Γ (graph (positiveFields j) w env (SyntaxAtomSyntax.three x i y j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun z => Fin.elim0 z)))
  have hchild : Derives Γ (ProjectionExprQuery.query positivePremise w env) :=
    .impE (.conjR (ProjectionTracePremises.get_variables_iff hZ (1 : Fin 4) 2 3 w env hw hn)) hq
  have hqparent := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.fieldPositive (by simp [ObjectProjection.rules]) w env hw hn
    (Derives.conjI hchild HornRuleSyntax.truth_proved)
  have he := ProjectionExprQuery.constructor_query_iff hZ 3 2 positiveFields w env (SyntaxAtomSyntax.three x i y) hw hn hs
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) positive_head) hqparent)

end PPAC.Migration.Internal.ProjectionFieldConstructors
