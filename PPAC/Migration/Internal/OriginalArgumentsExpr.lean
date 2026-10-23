import PPAC.Migration.Internal.OriginalTransformRowSyntax

/-! 原nil/cons实际head和两个实际前提的五字段数值对应，不替换原List编码。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments cons)

def nilFields : Fin 5 → Expr 3 := HornRowFields.five (.var 0) (.var 1) (.var 2) (Expr.list []) (Expr.list [])

def consFields : Fin 5 → Expr 7 := HornRowFields.five (.var 0) (.var 1) (.var 2) (cons (.var 3) (.var 4)) (cons (.var 5) (.var 6))

def headIndices : Fin 5 → Fin 7 := HornRowFields.five 0 1 2 3 5

def tailIndices : Fin 5 → Fin 7 := HornRowFields.five 0 1 2 4 6

theorem actual_nil_head : nilArguments.head = Expr.node (.literal 2) (List.ofFn nilFields) := rfl

theorem actual_cons_head : consArguments.head = Expr.node (.literal 2) (List.ofFn consFields) := rfl

theorem actual_head_premise : OriginalArgumentsTraceRules.headPremise = Expr.node (.literal 1) (List.ofFn (fun i => Expr.var (headIndices i))) := rfl

theorem actual_tail_premise : OriginalArgumentsTraceRules.tailPremise = Expr.node (.literal 2) (List.ofFn (fun i => Expr.var (tailIndices i))) := rfl

theorem variable_row_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat) (indices : Fin 5 → Fin n)
    (w r : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((graph (Expr.node (.literal kind) (List.ofFn (fun i => Expr.var (indices i)))) w env r).iff
      (SyntaxNodeSyntax.constructor 5 kind w (fun i => env (indices i)) r)) :=
  HornExprConstructor.constructor_iff hZ 5 kind _ w r env _ hw hn (fun i => .conjI (environmentNat_at w env hn (indices i)) (.eqRefl _))

theorem head_premise_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((graph OriginalArgumentsTraceRules.headPremise w env r).iff
      (OriginalTransformRowSyntax.row 1 w (env 0) (env 1) (env 2) (env 3) (env 5) r)) := by
  rw [actual_head_premise]
  simpa only [headIndices, FreeWeakenResultSyntax.five_map, OriginalTransformRowSyntax.row] using variable_row_iff hZ 1 headIndices w r env hw hn

theorem tail_premise_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((graph OriginalArgumentsTraceRules.tailPremise w env r).iff
      (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) (env 4) (env 6) r)) := by
  rw [actual_tail_premise]
  simpa only [tailIndices, FreeWeakenResultSyntax.five_map, OriginalTransformRowSyntax.row] using variable_row_iff hZ 2 tailIndices w r env hw hn

theorem nil_head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hnil : Derives Γ (StructuralListSyntax.nilCode w n)) (hqnil : Derives Γ (StructuralListSyntax.nilCode w q)) :
    Derives Γ ((graph nilArguments.head w env r).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) := by
  have hv (i : Fin 3) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hs : ∀ i, Derives Γ (graph (nilFields i) w env (HornRowFields.five (env 0) (env 1) (env 2) n q i)) := by
    intro i
    exact Fin.cases (hv 0) (fun j => Fin.cases (hv 1) (fun k => Fin.cases (hv 2) (fun l => Fin.cases (HornExprStructural.nil_graph w n env hnil) (fun _ => HornExprStructural.nil_graph w q env hqnil) l) k) j) i
  rw [actual_nil_head]
  exact HornExprConstructor.constructor_iff hZ 5 2 nilFields w r env _ hw hn hs

theorem cons_head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hC : Derives Γ (StructuralListSyntax.consCode w (env 5) (env 6) q)) :
    Derives Γ ((graph consArguments.head w env r).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) := by
  have hv (i : Fin 7) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hfirst := HornExprStructural.cons_graph (.var 3) (.var 4) w (env 3) (env 4) n env (hv 3) (hv 4) hc
  have hsecond := HornExprStructural.cons_graph (.var 5) (.var 6) w (env 5) (env 6) q env (hv 5) (hv 6) hC
  have hs : ∀ i, Derives Γ (graph (consFields i) w env (HornRowFields.five (env 0) (env 1) (env 2) n q i)) := by
    intro i
    exact Fin.cases (hv 0) (fun j => Fin.cases (hv 1) (fun k => Fin.cases (hv 2) (fun l => Fin.cases hfirst (fun _ => hsecond) l) k) j) i
  rw [actual_cons_head]
  exact HornExprConstructor.constructor_iff hZ 5 2 consFields w r env _ hw hn hs

end PPAC.Migration.Internal.OriginalArgumentsExpr
