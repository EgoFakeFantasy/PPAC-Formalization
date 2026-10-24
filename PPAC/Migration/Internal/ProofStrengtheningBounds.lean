import PPAC.Migration.Internal.ProofStrengtheningAllQueries
import PPAC.Migration.Internal.ProofSubstitutionBounds

/-! 原strengthening第四赋值由真实前驱字段取界；不要求任一前驱证明已经合法。 -/
namespace PPAC.Migration.Internal.ProofStrengtheningBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofStrengtheningSyntax
open NaturalAdditionBounds (below)
open YesMetaZFC.Automation

theorem predecessorFormula_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hq : Derives Γ (ProjectionExprQuery.query predecessorFormulaQuery w env)) : Derives Γ (below (env 3) (env 2)) :=
  ProofSubstitutionBounds.atOne_bound hZ w (env 2) (env 3) hw (environmentNat_at w env hn 2)
    (.impE (.conjL (ProofStrengtheningQueries.predecessorFormula_iff hZ w env hw hn)) hq)

theorem head_first_variables : ∀ j : Fin 3, j.castSucc ∈ ObjectProofNode.strengtheningShape.head.variables := by decide

theorem environment_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hh : Derives Γ (graph ObjectProofNode.strengtheningShape.head w env row))
    (hq : Derives Γ (ProjectionExprQuery.query predecessorFormulaQuery w env)) :
    Derives Γ (HornExprBounds.environmentBound 4 row env) := by
  have hr := HornExprRange.range hZ ObjectProofNode.strengtheningShape.head w row env hw hn hh
  have hb2 := HornExprBounds.variable_bound hZ ObjectProofNode.strengtheningShape.head (2 : Fin 4) (by decide) w row env hw hn hh
  have h42 := predecessorFormula_bound hZ w env hw hn hq
  have hb4 := NaturalOrderBasic.transitive hZ w (env 3) (env 2) row hw hr h42 hb2
  apply HornExprBounds.intro_environmentBound row env
  exact Fin.lastCases hb4 (fun j => HornExprBounds.variable_bound hZ ObjectProofNode.strengtheningShape.head j.castSucc
    (head_first_variables j) w row env hw hn hh)

theorem head_constructor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph ObjectProofNode.strengtheningShape.head w env row).iff
      (SyntaxNodeSyntax.constructor 3 4 w (fun j : Fin 3 => env j.castSucc) row)) := by
  have he : ObjectProofNode.strengtheningShape.head = YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 4)
      (List.ofFn (fun j : Fin 3 => YesMetaZFC.Automation.ObjectHorn.Expr.var j.castSucc)) := rfl
  rw [he]
  exact HornExprConstructor.constructor_iff hZ 3 4 (fun j : Fin 3 => .var j.castSucc) w row env (fun j : Fin 3 => env j.castSucc) hw hn
    (fun j => .conjI (environmentNat_at w env hn j.castSucc) (.eqRefl _))

end PPAC.Migration.Internal.ProofStrengtheningBounds
