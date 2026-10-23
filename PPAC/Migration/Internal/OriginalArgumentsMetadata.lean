import PPAC.Migration.Internal.OriginalRowMetadataSubstitution

/-! 原arity赋值头的真实前三字段恢复，以及五字段行的内部自然元数据。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsMetadata
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments)

theorem field_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (w mode depth parameter input output r : Fin m) (i : Fin 5)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter input output r)) :
    Derives Γ (.mem (HornRowFields.five mode depth parameter input output i) w) :=
  StructuralListTraceOrder.member_member hZ _ _ _ hw (SyntaxNodeInjective.constructor_range hZ 5 kind _ _ _ hw hr)
    (SyntaxConstructors.child_member hZ 5 kind _ _ _ i hw hr)

theorem metadata_eq {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (es : Fin 5 → Expr a) (j0 j1 j2 : Fin a)
    (e0 : es 0 = .var j0) (e1 : es 1 = .var j1) (e2 : es 2 = .var j2)
    (w mode depth parameter input output r : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hh : Derives Γ (graph (Expr.node (.literal 2) (List.ofFn es)) w env r))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r)) :
    Derives Γ ((Formula.equal mode (env j0)).conj ((Formula.equal depth (env j1)).conj (.equal parameter (env j2)))) := by
  have h0 := HornRowFields.field_graph hZ 2 es w r env (HornRowFields.five mode depth parameter input output) 0 hw hn hh hc
  have h1 := HornRowFields.field_graph hZ 2 es w r env (HornRowFields.five mode depth parameter input output) 1 hw hn hh hc
  have h2 := HornRowFields.field_graph hZ 2 es w r env (HornRowFields.five mode depth parameter input output) 2 hw hn hh hc
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  exact .conjI (.conjR h0) (.conjI (.conjR h1) (.conjR h2))

theorem nil_metadata {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter input output r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph nilArguments.head w env r))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r)) :
    Derives Γ ((Formula.equal mode (env 0)).conj ((Formula.equal depth (env 1)).conj (.equal parameter (env 2)))) := by
  rw [OriginalArgumentsExpr.actual_nil_head] at hh
  exact metadata_eq hZ OriginalArgumentsExpr.nilFields 0 1 2 rfl rfl rfl w mode depth parameter input output r env hw hn hh hc

theorem cons_metadata {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter input output r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hh : Derives Γ (graph consArguments.head w env r))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r)) :
    Derives Γ ((Formula.equal mode (env 0)).conj ((Formula.equal depth (env 1)).conj (.equal parameter (env 2)))) := by
  rw [OriginalArgumentsExpr.actual_cons_head] at hh
  exact metadata_eq hZ OriginalArgumentsExpr.consFields 0 1 2 rfl rfl rfl w mode depth parameter input output r env hw hn hh hc

end PPAC.Migration.Internal.OriginalArgumentsMetadata
