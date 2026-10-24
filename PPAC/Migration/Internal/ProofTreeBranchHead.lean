import PPAC.Migration.Internal.ProofTreeZeroGuard
import PPAC.Migration.Internal.ProofTreeTraceQuery

/-! 原六形状头表达式与精确数值构造器的对应；不使用宿主求值。 -/
namespace PPAC.Migration.Internal.ProofTreeBranchHead
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem payload_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (s : ObjectProofTree.Shape)
    (w p : Fin m) (env : Fin (s.extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat (s.extra+2) w env)) :
    Derives Γ ((graph (ObjectProofTree.payload s) w env p).iff (SyntaxNodeSyntax.constructor (s.extra+2) s.tag w env p)) :=
  HornExprConstructor.constructor_iff hZ (s.extra+2) s.tag ObjectHorn.Expr.var w p env env hw hn
    (fun i => .conjI (environmentNat_at w env hn i) (.eqRefl _))

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (s : ObjectProofTree.Shape)
    (w r p : Fin m) (env : Fin (s.extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat (s.extra+2) w env)) (hp : Derives Γ (graph (ObjectProofTree.payload s) w env p)) :
    Derives Γ ((graph (ObjectProofTree.branch s false).head w env r).iff (SyntaxNodeSyntax.constructor 1 0 w (fun _ => p) r)) := by
  exact HornExprConstructor.constructor_iff hZ 1 0 (fun _ => ObjectProofTree.payload s) w r env (fun _ => p) hw hn (fun _ => hp)

theorem root_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (s : ObjectProofTree.Shape)
    (w r p : Fin m) (env : Fin (s.extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat (s.extra+2) w env)) (hp : Derives Γ (graph (ObjectProofTree.payload s) w env p)) :
    Derives Γ ((graph (ObjectProofTree.branch s true).head w env r).iff (SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 p (env 1)) r)) := by
  apply HornExprConstructor.constructor_iff hZ 2 1 (SetLanguage.args2 (ObjectProofTree.payload s) (.var 1)) w r env (SetLanguage.args2 p (env 1)) hw hn
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp
  · refine Fin.cases ?_ (fun i => Fin.elim0 i) j
    exact .conjI (environmentNat_at w env hn 1) (.eqRefl _)

theorem premise_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (s : ObjectProofTree.Shape)
    (w p : Fin m) (env : Fin (s.extra+2) → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat (s.extra+2) w env)) (hp : Derives Γ (graph (ObjectProofTree.payload s) w env p)) :
    Derives Γ ((ProofTreeTracedStep.premise test (.node (.literal 0) [ObjectProofTree.payload s]) w env).iff (ProofTreeEntrySyntax.node test w p)) :=
  ProofTreeTraceQuery.constructor_query_iff test hZ 1 0 (fun _ => ObjectProofTree.payload s) w env (fun _ => p) hw hn (fun _ => hp)

end PPAC.Migration.Internal.ProofTreeBranchHead
