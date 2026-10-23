import PPAC.Migration.Internal.HornExprConstructor

/-! 固定上游lookupHead/lookupTail的真实表达式，字段赋值及候选行码全部内部化。 -/
namespace PPAC.Migration.Internal.OriginalLookupExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (lookupHead lookupTail cons)

def rowFields {m} (a b c : Fin m) : Fin 3 → Fin m := Fin.cases a (Fin.cases b (fun _ => c))

def headFields : Fin 3 → Expr 2 := Fin.cases (cons (.var 0) (.var 1)) (Fin.cases (.literal 0) (fun _ => .var 0))

def tailFields : Fin 3 → Expr 4 := Fin.cases (cons (.var 0) (.var 1)) (Fin.cases (.succ (.var 2)) (fun _ => .var 3))

def premiseFields : Fin 3 → Expr 4 := Fin.cases (.var 1) (Fin.cases (.var 2) (fun _ => .var 3))

def premiseExpr : Expr 4 := Expr.node (.literal 0) (List.ofFn premiseFields)

theorem actual_head_expression : lookupHead.head = Expr.node (.literal 0) (List.ofFn headFields) := rfl

theorem actual_tail_expression : lookupTail.head = Expr.node (.literal 0) (List.ofFn tailFields) := rfl

theorem actual_tail_premises : lookupTail.premises = [premiseExpr] := rfl

theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z row : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n)) (hz : Derives Γ (empty z)) :
    Derives Γ ((graph lookupHead.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (rowFields n z (env 0)) row)) := by
  have hv (i : Fin 2) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl (env i))
  have hs : ∀ i, Derives Γ (graph (headFields i) w env (rowFields n z (env 0) i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact HornExprStructural.cons_graph (.var 0) (.var 1) _ _ _ _ _ (hv 0) (hv 1) hc
    · exact Fin.cases hz (fun _ => hv 0) j
  rw [actual_head_expression]
  exact HornExprConstructor.constructor_iff hZ 3 0 headFields w row env (rowFields n z (env 0)) hw hn hs

theorem tail_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n)) (hs : Derives Γ (successor s (env 2))) :
    Derives Γ ((graph lookupTail.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (rowFields n s (env 3)) row)) := by
  have hv (i : Fin 4) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl (env i))
  have hh : ∀ i, Derives Γ (graph (tailFields i) w env (rowFields n s (env 3) i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact HornExprStructural.cons_graph (.var 0) (.var 1) _ _ _ _ _ (hv 0) (hv 1) hc
    · exact Fin.cases (intro_succ (.var 2) _ _ _ _ (hv 2) hs) (fun _ => hv 3) j
  rw [actual_tail_expression]
  exact HornExprConstructor.constructor_iff hZ 3 0 tailFields w row env (rowFields n s (env 3)) hw hn hh

theorem premise_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph premiseExpr w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (rowFields (env 1) (env 2) (env 3)) row)) := by
  have hv (i : Fin 4) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl (env i))
  have hs : ∀ i, Derives Γ (graph (premiseFields i) w env (rowFields (env 1) (env 2) (env 3) i)) := by
    intro i
    refine Fin.cases (hv 1) (fun j => Fin.cases (hv 2) (fun _ => hv 3) j) i
  exact HornExprConstructor.constructor_iff hZ 3 0 premiseFields w row env _ hw hn hs

end PPAC.Migration.Internal.OriginalLookupExpr
