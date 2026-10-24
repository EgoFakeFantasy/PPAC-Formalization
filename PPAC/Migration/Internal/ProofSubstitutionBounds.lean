import PPAC.Migration.Internal.RawCodeFieldBounds
import PPAC.Migration.Internal.ProofSubstitutionAllQueries

/-! 原替换节点全部六赋值的真实搜索界；第六值由原field数值界取得，不假定前驱合法。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofSubstitutionProjectionSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem atOne_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p y : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (ho : Derives Γ (atOne w p y)) : Derives Γ (below y p) := by
  let B := (SyntaxNumeralSyntax.numeral 1 (Fin.last m)).conj (RawCodeFieldSyntax.field w.castSucc p.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ho
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxNumerals.range hZ1 1 w.castSucc (Fin.last m) hw1 (.conjL hB)
  have hb := RawCodeFieldBounds.bound hZ1 _ _ _ _ hw1 (under hp B) hi (.conjR hB)
  exact of_eq (below_rename y p Fin.castSucc).symm hb

theorem formula_projection_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hq : Derives Γ (ProjectionExprQuery.query formulaProjection w env)) : Derives Γ (below (env 5) (env 4)) :=
  atOne_bound hZ w (env 4) (env 5) hw (environmentNat_at w env hn 4)
    (.impE (.conjL (ProofSubstitutionProjection.formula_query_iff hZ w env hw hn)) hq)

theorem head_first_variables : ∀ j : Fin 5, j.castSucc ∈ ObjectProofNode.substitutionShape.head.variables := by decide

theorem environment_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hh : Derives Γ (graph ObjectProofNode.substitutionShape.head w env row))
    (hq : Derives Γ (ProjectionExprQuery.query formulaProjection w env)) :
    Derives Γ (HornExprBounds.environmentBound 6 row env) := by
  have hr := HornExprRange.range hZ ObjectProofNode.substitutionShape.head w row env hw hn hh
  have hb4 := HornExprBounds.variable_bound hZ ObjectProofNode.substitutionShape.head (4 : Fin 6) (by decide) w row env hw hn hh
  have h54 := formula_projection_bound hZ w env hw hn hq
  have hb5 := NaturalOrderBasic.transitive hZ w (env 5) (env 4) row hw hr h54 hb4
  apply HornExprBounds.intro_environmentBound row env
  exact Fin.lastCases hb5 (fun j => HornExprBounds.variable_bound hZ ObjectProofNode.substitutionShape.head j.castSucc
    (head_first_variables j) w row env hw hn hh)

theorem head_constructor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) :
    Derives Γ ((graph ObjectProofNode.substitutionShape.head w env row).iff
      (SyntaxNodeSyntax.constructor 5 5 w (fun j : Fin 5 => env j.castSucc) row)) := by
  have he : ObjectProofNode.substitutionShape.head = YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 5)
      (List.ofFn (fun j : Fin 5 => YesMetaZFC.Automation.ObjectHorn.Expr.var j.castSucc)) := rfl
  rw [he]
  exact HornExprConstructor.constructor_iff hZ 5 5 (fun j : Fin 5 => .var j.castSucc) w row env (fun j : Fin 5 => env j.castSucc) hw hn
    (fun j => .conjI (environmentNat_at w env hn j.castSucc) (.eqRefl _))

end PPAC.Migration.Internal.ProofSubstitutionBounds
