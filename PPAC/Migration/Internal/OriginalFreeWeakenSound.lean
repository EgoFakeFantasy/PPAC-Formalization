import PPAC.Migration.Internal.FreeWeakenValue

/-! 原freeWeaken头图与三变量存在应用反向取得实际后继自由变量值。 -/
namespace PPAC.Migration.Internal.OriginalFreeWeakenSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (freeWeaken varCode)

def fields : Fin 5 → Expr 3 := HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.succ (.var 2)))

theorem actual_head : freeWeaken.head = Expr.node (.literal 1) (List.ofFn fields) := rfl

theorem matrix_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix freeWeaken w r R env)) : Derives Γ (FreeWeakenValueSyntax.shifted w idx (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn fields)) w env r) := .conjL hm
  have hf3 := HornRowFields.field_graph hZ 1 fields w r env xs 3 hw hn hg hc
  have hf4 := HornRowFields.field_graph hZ 1 fields w r env xs 4 hw hn hg hc
  have hi : Derives Γ (graph (.var 2) w env (env 2)) := .conjI (environmentNat_at w env hn 2) (.eqRefl _)
  have hcode := HornVariableValue.graph_code hZ false (.var 2) w (env 2) (xs 3) env hw hn hi hf3
  have hei := SyntaxVariableDecode.index_eq hZ false w (env 2) idx (xs 3) hw hcode hv
  have he := InsertExistence.exists_insert (env 2) (env 2) (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let S := successor (Fin.last m) (env 2).castSucc
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) he
  have hZ1 := ZFContext.under hZ S
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hn1 : Derives Δ (environmentNat 3 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn S)
  have hi1 : Derives Δ (graph (.var 2) w.castSucc (fun i => (env i).castSucc) (env 2).castSucc) := of_eq (graph_rename _ w (env 2) env Fin.castSucc) (under hi S)
  have hf1 : Derives Δ (graph (varCode true (.succ (.var 2))) w.castSucc (fun i => (env i).castSucc) (xs 4).castSucc) := of_eq (graph_rename _ w (xs 4) env Fin.castSucc) (under hf4 S)
  have hei1 : Derives Δ (.equal (env 2).castSucc idx.castSucc) := under hei S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hsgraph := intro_succ (.var 2) _ _ _ _ hi1 hS
  have hout := HornVariableValue.graph_code hZ1 false (.succ (.var 2)) _ _ _ _ hw1 hn1 hsgraph hf1
  have hs := FreeWeakenValueSyntax.successor_input_subst _ _ _ hei1 hS
  have ho := FreeWeakenValueSyntax.intro_shifted _ _ _ _ hs hout
  exact of_eq (FreeWeakenValueSyntax.shifted_rename w idx (xs 4) Fin.castSucc).symm ho

theorem application_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ha : Derives Γ (application freeWeaken w r R)) : Derives Γ (FreeWeakenValueSyntax.shifted w idx (xs 4)) := by
  let B := body freeWeaken w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application freeWeaken w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old 3 w) (fun i => old 3 (xs i)) (old 3 r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false (old 3 w) (old 3 idx) (old 3 (xs 3))) := of_eq
    (SyntaxVariableSyntax.code_rename false w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := matrix_shifted hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (FreeWeakenValueSyntax.shifted_rename w idx (xs 4) (old 3)).symm ho

end PPAC.Migration.Internal.OriginalFreeWeakenSound
