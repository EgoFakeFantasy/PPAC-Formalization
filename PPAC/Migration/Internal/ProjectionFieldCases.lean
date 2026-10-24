import PPAC.Migration.Internal.ProjectionFieldConstructors

/-! 原field局部应用数值可靠性，实际get子查询由真实原根集合取出。 -/
namespace PPAC.Migration.Internal.ProjectionFieldCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem zero_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hh : Derives Γ (graph ObjectProjection.fieldZero.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.fieldRow w x i y row)) :
    Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  have hx := HornNodeFields.field_3 hZ 2 ProjectionGetConstructors.zeroFields w row env (SyntaxAtomSyntax.three x i y) 0 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionFieldConstructors.zero_head) hh) hr
  have hy := HornNodeFields.field_3 hZ 2 ProjectionGetConstructors.zeroFields w row env (SyntaxAtomSyntax.three x i y) 2 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionFieldConstructors.zero_head) hh) hr
  have hi := ProjectionNodeFields.constructor_field_natural hZ 3 2 w row (SyntaxAtomSyntax.three x i y) 1 hw hr
  exact .impE (.conjR (RawCodeField.zero_iff hZ w x i y hw hx hi)) hy

theorem positive_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hh : Derives Γ (graph ObjectProjection.fieldPositive.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.fieldRow w x i y row))
    (hq : Derives Γ (ProjectionTraceSyntax.get w (env 1) (env 2) (env 3))) : Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  have hx := HornNodeFields.field_3 hZ 2 ProjectionFieldConstructors.positiveFields w row env (SyntaxAtomSyntax.three x i y) 0 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionFieldConstructors.positive_head) hh) hr
  have hi := HornNodeFields.field_3 hZ 2 ProjectionFieldConstructors.positiveFields w row env (SyntaxAtomSyntax.three x i y) 1 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionFieldConstructors.positive_head) hh) hr
  have hy := HornNodeFields.field_3 hZ 2 ProjectionFieldConstructors.positiveFields w row env (SyntaxAtomSyntax.three x i y) 2 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionFieldConstructors.positive_head) hh) hr
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hraw := Derives.impE (.conjL (HornExprStructural.raw_iff hZ (.var 0) (.var 1) w (env 0) (env 1) x env hw hn (hv 0) (hv 1))) hx
  have hget := ProjectionGetInduction.checked_sound hZ w (env 1) (env 2) (env 3) hw hq
  have hg1 := RawCodeGetSyntax.index_subst w (env 1) (env 2) i (env 3) (eq_symm (.conjR hi)) hget
  have hg2 := RawCodeGetSyntax.output_subst w (env 1) i (env 3) y (eq_symm (.conjR hy)) hg1
  exact .impE (.conjR (RawCodeField.on_raw_iff hZ w (env 0) (env 1) x i y hw
    (environmentNat_at w env hn 0) (environmentNat_at w env hn 1) hraw)) hg2

theorem zero_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row V : Fin m)
    (hw : Derives Γ (omega w))
    (hr : Derives Γ (ProjectionTraceSyntax.fieldRow w x i y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.fieldZero w row V)) :
    Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  let B := HornApplicationSyntax.body ObjectProjection.fieldZero w row V
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.fieldZero w row V _ ha
  have hZ1 := HornBinderRules.zf_body 1 hZ B
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.fieldRow (old 1 w) (old 1 x) (old 1 i) (old 1 y) (old 1 row)) :=
    of_eq (ProjectionTraceSyntax.fieldRow_rename w x i y row (old 1)) (HornBinderRules.under_body 1 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := zero_sound hZ1 _ _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1
  exact of_eq (RawCodeFieldSyntax.field_rename w x i y (old 1)).symm ho

theorem positive_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hr : Derives Γ (ProjectionTraceSyntax.fieldRow w x i y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.fieldPositive w row V)) :
    Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  let B := HornApplicationSyntax.body ObjectProjection.fieldPositive w row V
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.fieldPositive w row V _ ha
  have hZ1 := HornBinderRules.zf_body 4 hZ B
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.fieldRow (old 4 w) (old 4 x) (old 4 i) (old 4 y) (old 4 row)) :=
    of_eq (ProjectionTraceSyntax.fieldRow_rename w x i y row (old 4)) (HornBinderRules.under_body 4 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv1 : Derives Δ (ProjectionTraceSetSyntax.value (old 4 w) (old 4 V)) :=
    of_eq (ProjectionTraceSetSyntax.value_rename w V (old 4)) (HornBinderRules.under_body 4 hv B)
  have hpre : Derives Δ (HornRuleSyntax.premise ProjectionFieldConstructors.positivePremise (old 4 w) (old 4 V) (slot 4)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR hB))))
  have hquery := Derives.impE (.conjL (ProjectionTracePremises.premise_iff ProjectionFieldConstructors.positivePremise (old 4 w) (old 4 V) (slot 4) hv1)) hpre
  have hchild := Derives.impE (.conjL (ProjectionTracePremises.get_variables_iff hZ1 (1 : Fin 4) 2 3 (old 4 w) (slot 4) hw1 (.conjL hB))) hquery
  have ho := positive_sound hZ1 _ _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1 hchild
  exact of_eq (RawCodeFieldSyntax.field_rename w x i y (old 4)).symm ho

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hr : Derives Γ (ProjectionTraceSyntax.fieldRow w x i y row)) (ht : Derives Γ (ProjectionTraceSyntax.condition w row)) :
    Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  have hs := ProjectionRuleDispatch.field_step hZ 3 w row V (SyntaxAtomSyntax.three x i y) hw hr
    (ProjectionTraceUnfold.condition_step w V row hv ht)
  apply HornStepSyntax.step_elim ProjectionRuleDispatch.fieldRules w row V _ hs
  intro rule hm
  apply Derives.impI
  simp only [ProjectionRuleDispatch.fieldRules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact zero_application (ZFContext.add hZ _) w x i y row V (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact positive_application (ZFContext.add hZ _) w x i y row V (add hw _) (add hv _) (add hr _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProjectionFieldCases
