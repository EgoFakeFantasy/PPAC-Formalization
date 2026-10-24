import PPAC.Migration.Internal.ProofLogicalSyntax

/-! 逻辑证明节点的两个实际三字段头、查询行码EX和全部赋值界。 -/
namespace PPAC.Migration.Internal.ProofLogicalQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofLogicalSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((graph ObjectProofNode.logicalShape.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (headFields env) row)) := by
  exact HornExprConstructor.constructor_iff hZ 3 0 (fun i : Fin 3 => Expr.var i) w row env (headFields env) hw hn
    (fun i => .conjI (environmentNat_at w env hn i) (.eqRefl _))

theorem query_constructor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((bundle w env).iff (OriginalLogicalExprQuery.rowQuery 3 0 w (queryFields env))) := by
  let es : Fin 3 → Expr 3 := Fin.cases (.var 0) (Fin.cases (.var 2) (Fin.cases (.var 1) Fin.elim0))
  have he : queryExpr = Expr.node (.literal 0) (List.ofFn es) := rfl
  change Derives Γ ((OriginalLogicalExprQuery.query queryExpr w env).iff _)
  rw [he]
  apply OriginalLogicalExprQuery.constructor_query_iff hZ 3 0 es w env (queryFields env) hw hn
  intro i
  refine Fin.cases (.conjI (environmentNat_at w env hn 0) (.eqRefl _)) (fun j => ?_) i
  refine Fin.cases (.conjI (environmentNat_at w env hn 2) (.eqRefl _)) (fun k => ?_) j
  exact Fin.cases (.conjI (environmentNat_at w env hn 1) (.eqRefl _)) (fun q => Fin.elim0 q) k

theorem query_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle w env).iff (specification w z env)) := by
  apply SyntaxTypeLocalTransfer.iff_trans (query_constructor_iff hZ w env hw hn)
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (HornBinderRules.under_many 1 hw)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (HornBinderRules.under_many 1 hz)
  exact LogicalOriginalNodes.table_iff (HornBinderRules.zf_many 1 hZ) w.castSucc z.castSucc (Fin.last m) hw1 hz1

theorem all_assignment_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph ObjectProofNode.logicalShape.head w env row)) : Derives Γ (HornExprBounds.environmentBound 3 row env) := by
  have hVars : ∀ i, i ∈ ObjectProofNode.logicalShape.head.variables := by decide
  exact HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ ObjectProofNode.logicalShape.head i (hVars i) w row env hw hn hh)

end PPAC.Migration.Internal.ProofLogicalQueries
