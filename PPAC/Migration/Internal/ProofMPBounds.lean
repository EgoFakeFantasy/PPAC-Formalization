import PPAC.Migration.Internal.ProofMPAllQueries
import PPAC.Migration.Internal.ProofSubstitutionBounds

/-! 原MP第五赋值由真实左前驱字段取界；不要求任一前驱证明已经合法。 -/
namespace PPAC.Migration.Internal.ProofMPBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofMPSyntax
open NaturalAdditionBounds (below)
open YesMetaZFC.Automation

theorem leftFormula_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hq : Derives Γ (ProjectionExprQuery.query leftFormulaQuery w env)) : Derives Γ (below (env 4) (env 2)) :=
  ProofSubstitutionBounds.atOne_bound hZ w (env 2) (env 4) hw (environmentNat_at w env hn 2)
    (.impE (.conjL (ProofMPQueries.leftFormula_iff hZ w env hw hn)) hq)

theorem head_first_variables : ∀ j : Fin 4, j.castSucc ∈ ObjectProofNode.mpShape.head.variables := by decide

theorem environment_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hh : Derives Γ (graph ObjectProofNode.mpShape.head w env row))
    (hq : Derives Γ (ProjectionExprQuery.query leftFormulaQuery w env)) :
    Derives Γ (HornExprBounds.environmentBound 5 row env) := by
  have hr := HornExprRange.range hZ ObjectProofNode.mpShape.head w row env hw hn hh
  have hb2 := HornExprBounds.variable_bound hZ ObjectProofNode.mpShape.head (2 : Fin 5) (by decide) w row env hw hn hh
  have h42 := leftFormula_bound hZ w env hw hn hq
  have hb4 := NaturalOrderBasic.transitive hZ w (env 4) (env 2) row hw hr h42 hb2
  apply HornExprBounds.intro_environmentBound row env
  exact Fin.lastCases hb4 (fun j => HornExprBounds.variable_bound hZ ObjectProofNode.mpShape.head j.castSucc
    (head_first_variables j) w row env hw hn hh)

theorem head_constructor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) :
    Derives Γ ((graph ObjectProofNode.mpShape.head w env row).iff
      (SyntaxNodeSyntax.constructor 4 2 w (fun j : Fin 4 => env j.castSucc) row)) := by
  have he : ObjectProofNode.mpShape.head = YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 2)
      (List.ofFn (fun j : Fin 4 => YesMetaZFC.Automation.ObjectHorn.Expr.var j.castSucc)) := rfl
  rw [he]
  exact HornExprConstructor.constructor_iff hZ 4 2 (fun j : Fin 4 => .var j.castSucc) w row env (fun j : Fin 4 => env j.castSucc) hw hn
    (fun j => .conjI (environmentNat_at w env hn j.castSucc) (.eqRefl _))

end PPAC.Migration.Internal.ProofMPBounds
