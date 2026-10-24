import PPAC.Migration.Internal.ProjectionRawPairExpr
import PPAC.Migration.Internal.ProjectionRuleConstruction
import PPAC.Migration.Internal.ProjectionNodeFields

/-! 三条原get规则的真实头、子前提及父查询构造；行码和赋值块见证不作为外部输入。 -/
namespace PPAC.Migration.Internal.ProjectionGetConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def zeroFields : Fin 3 → Expr 1 := ProjectionTracePremises.three (Expr.literal 0) (.var 0) (.literal 0)
def headFields : Fin 3 → Expr 3 := ProjectionTracePremises.three (ProjectionRawPairExpr.rawPair 0 1 2) (.literal 0) (.var 1)
def tailFields : Fin 3 → Expr 5 := ProjectionTracePremises.three (ProjectionRawPairExpr.rawPair 0 1 2) (.succ (.var 3)) (.var 4)
def tailPremise : Expr 5 := Expr.node (.literal 1) (List.ofFn (ProjectionTracePremises.getFields 2 3 4))

theorem zero_head : ObjectProjection.getZero.head = Expr.node (.literal 1) (List.ofFn zeroFields) := rfl
theorem head_head : ObjectProjection.getHead.head = Expr.node (.literal 1) (List.ofFn headFields) := rfl
theorem tail_head : ObjectProjection.getTail.head = Expr.node (.literal 1) (List.ofFn tailFields) := rfl
theorem tail_premises : ObjectProjection.getTail.premises = [tailPremise] := rfl

theorem zero_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hx : Derives Γ (empty x)) (hy : Derives Γ (empty y)) :
    Derives Γ (ProjectionTraceSyntax.get w x i y) := by
  let env : Fin 1 → Fin m := fun _ => i
  have hn : Derives Γ (environmentNat 1 w env) := HornApplicationRules.intro_nat w env (fun _ => hi)
  have h0 : Derives Γ (graph (zeroFields 0) w env x) := hx
  have h1 : Derives Γ (graph (zeroFields 1) w env i) := .conjI hi (.eqRefl _)
  have h2 : Derives Γ (graph (zeroFields 2) w env y) := hy
  have hs : ∀ j, Derives Γ (graph (zeroFields j) w env (SyntaxAtomSyntax.three x i y j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun z => Fin.elim0 z)))
  have hq := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.getZero (by simp [ObjectProjection.rules]) w env hw hn HornRuleSyntax.truth_proved
  have he := ProjectionExprQuery.constructor_query_iff hZ 3 1 zeroFields w env (SyntaxAtomSyntax.three x i y) hw hn hs
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) zero_head) hq)

theorem head_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag first rest p x z : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (ha : Derives Γ (.mem first w)) (hb : Derives Γ (.mem rest w))
    (hp : Derives Γ (GodelPairSyntax.code w first rest p)) (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x))
    (hz : Derives Γ (empty z)) : Derives Γ (ProjectionTraceSyntax.get w x z first) := by
  let env := SyntaxAtomSyntax.three tag first rest
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases ht (Fin.cases ha (Fin.cases hb (fun v => Fin.elim0 v))))
  have h0 : Derives Γ (graph (headFields 0) w env x) := ProjectionRawPairExpr.graph_of_code 0 1 2 w p x env hn hp hr
  have h1 : Derives Γ (graph (headFields 1) w env z) := hz
  have h2 : Derives Γ (graph (headFields 2) w env first) := .conjI ha (.eqRefl _)
  have hs : ∀ j, Derives Γ (graph (headFields j) w env (SyntaxAtomSyntax.three x z first j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun v => Fin.elim0 v)))
  have hq := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.getHead (by simp [ObjectProjection.rules]) w env hw hn HornRuleSyntax.truth_proved
  have he := ProjectionExprQuery.constructor_query_iff hZ 3 1 headFields w env (SyntaxAtomSyntax.three x z first) hw hn hs
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) head_head) hq)

theorem tail_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag first rest p x i s y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (ha : Derives Γ (.mem first w)) (hb : Derives Γ (.mem rest w))
    (hp : Derives Γ (GodelPairSyntax.code w first rest p)) (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x))
    (hs : Derives Γ (successor s i)) (hq : Derives Γ (ProjectionTraceSyntax.get w rest i y)) :
    Derives Γ (ProjectionTraceSyntax.get w x s y) := by
  have hi := ProjectionNodeFields.get_natural_at hZ w rest i y 1 hw hq
  have hy := ProjectionNodeFields.get_natural_at hZ w rest i y 2 hw hq
  let env := HornRowFields.five tag first rest i y
  have hn : Derives Γ (environmentNat 5 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases ht (Fin.cases ha (Fin.cases hb (Fin.cases hi (fun _ => hy)))))
  have h0 : Derives Γ (graph (tailFields 0) w env x) := ProjectionRawPairExpr.graph_of_code 0 1 2 w p x env hn hp hr
  have h1 : Derives Γ (graph (tailFields 1) w env s) := intro_succ (.var 3) w s i env (.conjI hi (.eqRefl _)) hs
  have h2 : Derives Γ (graph (tailFields 2) w env y) := .conjI hy (.eqRefl _)
  have hfields : ∀ j, Derives Γ (graph (tailFields j) w env (SyntaxAtomSyntax.three x s y j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun v => Fin.elim0 v)))
  have hchild : Derives Γ (ProjectionExprQuery.query tailPremise w env) :=
    .impE (.conjR (ProjectionTracePremises.get_variables_iff hZ (2 : Fin 5) 3 4 w env hw hn)) hq
  have hparent := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.getTail (by simp [ObjectProjection.rules]) w env hw hn
    (Derives.conjI hchild HornRuleSyntax.truth_proved)
  have he := ProjectionExprQuery.constructor_query_iff hZ 3 1 tailFields w env (SyntaxAtomSyntax.three x s y) hw hn hfields
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) tail_head) hparent)

theorem output_subst {m} {Γ : Context m} (w x i y z : Fin m) (he : Derives Γ (.equal y z))
    (hy : Derives Γ (ProjectionTraceSyntax.get w x i y)) : Derives Γ (ProjectionTraceSyntax.get w x i z) := by
  let P := ProjectionTraceSyntax.get w.castSucc x.castSucc i.castSucc (Fin.last m)
  have h0 : P.instantiate y = ProjectionTraceSyntax.get w x i y := by
    simp only [P, Formula.instantiate, ProjectionTraceSyntax.get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = ProjectionTraceSyntax.get w x i z := by
    simp only [P, Formula.instantiate, ProjectionTraceSyntax.get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

end PPAC.Migration.Internal.ProjectionGetConstructors
