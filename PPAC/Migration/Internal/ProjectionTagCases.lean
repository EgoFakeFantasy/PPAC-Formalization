import PPAC.Migration.Internal.ProjectionRuleDispatch
import PPAC.Migration.Internal.ProjectionRuleConstruction
import PPAC.Migration.Internal.PairingProjectionNatural

/-! 两条原tag规则的真实头字段及其数值可靠性，不预给输入的规范节点形状。 -/
namespace PPAC.Migration.Internal.ProjectionTagCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def zeroFields : Fin 2 → Expr 0 := SetLanguage.args2 (.literal 0) (.literal 0)
def positiveFields : Fin 2 → Expr 2 := SetLanguage.args2 (ObjectProjection.raw (.var 0) (.var 1)) (.var 0)

theorem zero_head : ObjectProjection.tagZero.head = Expr.node (.literal 0) (List.ofFn zeroFields) := rfl
theorem positive_head : ObjectProjection.tagPositive.head = Expr.node (.literal 0) (List.ofFn positiveFields) := rfl

theorem output_subst {m} {Γ : Context m} (w x y z : Fin m) (he : Derives Γ (.equal y z))
    (hy : Derives Γ (PairingProjectionSyntax.step true true w x y)) : Derives Γ (PairingProjectionSyntax.step true true w x z) := by
  let P := PairingProjectionSyntax.step true true w.castSucc x.castSucc (Fin.last m)
  have h0 : P.instantiate y = PairingProjectionSyntax.step true true w x y := by
    simp only [P, Formula.instantiate, PairingProjectionSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = PairingProjectionSyntax.step true true w x z := by
    simp only [P, Formula.instantiate, PairingProjectionSyntax.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

theorem zero_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row : Fin m) (env : Fin 0 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 0 w env))
    (hh : Derives Γ (graph ObjectProjection.tagZero.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  have hx := ProjectionNodeFields.field_2 hZ 0 zeroFields w row env (SetLanguage.args2 x y) 0 hw hn (of_eq (congrArg (fun e => graph e w env row) zero_head) hh) hr
  have hy := ProjectionNodeFields.field_2 hZ 0 zeroFields w row env (SetLanguage.args2 x y) 1 hw hn (of_eq (congrArg (fun e => graph e w env row) zero_head) hh) hr
  change Derives Γ (empty x) at hx
  change Derives Γ (empty y) at hy
  exact .disjR (.conjI (PairingProjectionNatural.raw_zero_unselected true w x hx) hy)

theorem positive_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hh : Derives Γ (graph ObjectProjection.tagPositive.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  have hx := ProjectionNodeFields.field_2 hZ 0 positiveFields w row env (SetLanguage.args2 x y) 0 hw hn (of_eq (congrArg (fun e => graph e w env row) positive_head) hh) hr
  have hy := ProjectionNodeFields.field_2 hZ 0 positiveFields w row env (SetLanguage.args2 x y) 1 hw hn (of_eq (congrArg (fun e => graph e w env row) positive_head) hh) hr
  have ha := environmentNat_at w env hn 0
  have hb := environmentNat_at w env hn 1
  have hg0 : Derives Γ (graph (.var 0) w env (env 0)) := .conjI ha (.eqRefl _)
  have hg1 : Derives Γ (graph (.var 1) w env (env 1)) := .conjI hb (.eqRefl _)
  have hraw := Derives.impE (.conjL (HornExprStructural.raw_iff hZ (.var 0) (.var 1) w (env 0) (env 1) x env hw hn hg0 hg1)) hx
  have hs : Derives Γ (PairingProjectionSyntax.step true true w x (env 0)) := .disjL (PairingProjection.selected_code true true w (env 0) (env 1) x ha hb hraw)
  exact output_subst w x (env 0) y (eq_symm (.conjR hy)) hs

theorem zero_application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.tagZero w row R)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  let B := HornApplicationSyntax.body ObjectProjection.tagZero w row R
  let Δ := Context.add B (raisedContext 0 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.tagZero w row R _ ha
  have hw1 : Derives Δ (omega (old 0 w)) := of_eq (omega_rename w (old 0)) (HornBinderRules.under_body 0 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.tagRow (old 0 w) (old 0 x) (old 0 y) (old 0 row)) :=
    of_eq (ProjectionTraceSyntax.tagRow_rename w x y row (old 0)) (HornBinderRules.under_body 0 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := zero_sound (HornBinderRules.zf_body 0 hZ B) _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1
  exact of_eq (PairingProjectionSyntax.step_rename true true w x y (old 0)).symm ho

theorem positive_application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.tagPositive w row R)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  let B := HornApplicationSyntax.body ObjectProjection.tagPositive w row R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.tagPositive w row R _ ha
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.tagRow (old 2 w) (old 2 x) (old 2 y) (old 2 row)) :=
    of_eq (ProjectionTraceSyntax.tagRow_rename w x y row (old 2)) (HornBinderRules.under_body 2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := positive_sound (HornBinderRules.zf_body 2 hZ B) _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1
  exact of_eq (PairingProjectionSyntax.step_rename true true w x y (old 2)).symm ho

theorem step_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row))
    (hs : Derives Γ (HornStepSyntax.step ProjectionRuleDispatch.tagRules w row R)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  apply HornStepSyntax.step_elim ProjectionRuleDispatch.tagRules w row R _ hs
  intro rule hm
  apply Derives.impI
  simp only [ProjectionRuleDispatch.tagRules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact zero_application_sound (ZFContext.add hZ _) w x y row R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact positive_application_sound (ZFContext.add hZ _) w x y row R (add hw _) (add hr _) (.hyp (Or.inl rfl))

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y row : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.tagRow w x y row))
    (hc : Derives Γ (ProjectionTraceSyntax.condition w row)) : Derives Γ (PairingProjectionSyntax.step true true w x y) :=
  step_sound hZ w x y row w hw hr (ProjectionRuleDispatch.tag_step hZ 2 w row w (SetLanguage.args2 x y) hw hr
    (ProjectionTraceSyntax.condition_step w row hc))

end PPAC.Migration.Internal.ProjectionTagCases
