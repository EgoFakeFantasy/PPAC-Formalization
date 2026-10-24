import PPAC.Migration.Internal.ProjectionTraceSet
import PPAC.Migration.Internal.ProjectionExprQuery

/-! 真实原七规则根集合中的前提成员关系与原投影子查询双向对应。 -/
namespace PPAC.Migration.Internal.ProjectionTracePremises
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem premise_iff {m a} {Γ : Context m} (e : Expr a) (w V : Fin m) (env : Fin a → Fin m)
    (hv : Derives Γ (ProjectionTraceSetSyntax.value w V)) :
    Derives Γ ((HornRuleSyntax.premise e w V env).iff (ProjectionExprQuery.query e w env)) := by
  apply FormulaCodeCongruence.ex_congr
  have hv1 : Derives (Context.image Formula.raise Γ) (ProjectionTraceSetSyntax.value w.castSucc V.castSucc) :=
    of_eq (ProjectionTraceSetSyntax.value_rename w V Fin.castSucc) (.rename Fin.castSucc hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (ProjectionTraceSet.member_iff _ _ _ hv1)

theorem premises_iff {m a} {Γ : Context m} (es : List (Expr a)) (w V : Fin m) (env : Fin a → Fin m)
    (hv : Derives Γ (ProjectionTraceSetSyntax.value w V)) :
    Derives Γ ((HornRuleSyntax.premises es w V env).iff (ProjectionExprQuery.premises es w env)) := by
  induction es with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl _
  | cons e es ih => exact FormulaCodeCongruence.conj_congr (premise_iff e w V env hv) ih

def three {α : Type} (a b c : α) : Fin 3 → α := Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))

def getFields {a} (x i y : Fin a) : Fin 3 → Expr a := three (Expr.var x) (.var i) (.var y)

theorem get_variables_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (x i y : Fin a)
    (w : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((ProjectionExprQuery.query (Expr.node (.literal 1) (List.ofFn (getFields x i y))) w env).iff
      (ProjectionTraceSyntax.get w (env x) (env i) (env y))) := by
  have hs : ∀ j, Derives Γ (graph (getFields x i y j) w env (SyntaxAtomSyntax.three (env x) (env i) (env y) j)) := by
    intro j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun z => Fin.elim0 z) l) k) j
    · exact .conjI (environmentNat_at w env hn x) (.eqRefl _)
    · exact .conjI (environmentNat_at w env hn i) (.eqRefl _)
    · exact .conjI (environmentNat_at w env hn y) (.eqRefl _)
  exact ProjectionExprQuery.constructor_query_iff hZ 3 1 (getFields x i y) w env (SyntaxAtomSyntax.three (env x) (env i) (env y)) hw hn hs

end PPAC.Migration.Internal.ProjectionTracePremises
