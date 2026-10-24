import PPAC.Migration.Internal.ProjectionTagCases

/-! 原tag轨迹查询与实际数值投影在全部内部候选上双向等价；自然输入域保留于公式。 -/
namespace PPAC.Migration.Internal.ProjectionTag
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProjectionTagCases
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

theorem zero_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) (hy : Derives Γ (empty y)) :
    Derives Γ (ProjectionTraceSyntax.tag w x y) := by
  let env : Fin 0 → Fin m := Fin.elim0
  have hn : Derives Γ (environmentNat 0 w env) := HornRuleSyntax.truth_proved
  have hxg : Derives Γ (graph (zeroFields 0) w env x) := hx
  have hyg : Derives Γ (graph (zeroFields 1) w env y) := hy
  have hs : ∀ j, Derives Γ (graph (zeroFields j) w env (SetLanguage.args2 x y j)) :=
    Fin.cases hxg (Fin.cases hyg (fun z => Fin.elim0 z))
  have hq := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.tagZero
    (by simp [ObjectProjection.rules]) w env hw hn HornRuleSyntax.truth_proved
  have he := ProjectionExprQuery.constructor_query_iff hZ 2 0 zeroFields w env (SetLanguage.args2 x y) hw hn hs
  change Derives Γ (ProjectionExprQuery.rowQuery 2 0 w (SetLanguage.args2 x y))
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) zero_head) hq)

theorem positive_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y b : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (.mem y w)) (hb : Derives Γ (.mem b w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w y b x)) : Derives Γ (ProjectionTraceSyntax.tag w x y) := by
  let env := SetLanguage.args2 y b
  have hn : Derives Γ (environmentNat 2 w env) :=
    HornApplicationRules.intro_nat w env (Fin.cases hy (Fin.cases hb (fun z => Fin.elim0 z)))
  have hy1 : Derives Γ (graph (.var 0) w env y) := .conjI hy (.eqRefl _)
  have hb1 : Derives Γ (graph (.var 1) w env b) := .conjI hb (.eqRefl _)
  have hxg : Derives Γ (graph (positiveFields 0) w env x) := HornExprStructural.raw_graph (.var 0) (.var 1) w y b x env hy1 hb1 hr
  have hyg : Derives Γ (graph (positiveFields 1) w env y) := hy1
  have hs : ∀ j, Derives Γ (graph (positiveFields j) w env (SetLanguage.args2 x y j)) :=
    Fin.cases hxg (Fin.cases hyg (fun z => Fin.elim0 z))
  have hq := ProjectionRuleConstruction.query_from_rule hZ ObjectProjection.tagPositive
    (by simp [ObjectProjection.rules]) w env hw hn HornRuleSyntax.truth_proved
  have he := ProjectionExprQuery.constructor_query_iff hZ 2 0 positiveFields w env (SetLanguage.args2 x y) hw hn hs
  change Derives Γ (ProjectionExprQuery.rowQuery 2 0 w (SetLanguage.args2 x y))
  exact .impE (.conjL he) (of_eq (congrArg (fun e => ProjectionExprQuery.query e w env) positive_head) hq)

theorem selected_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (PairingProjectionSyntax.selected true true w x y)) :
    Derives Γ (ProjectionTraceSyntax.tag w x y) := by
  let B := PairingProjectionSyntax.body true true w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := positive_checked (ZFContext.under hZ B) w.castSucc x.castSucc y.castSucc (Fin.last m)
    hw1 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB)
  exact of_eq (ProjectionTraceSyntax.tag_rename w x y Fin.castSucc).symm ho

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w))
    (hy : Derives Γ (PairingProjectionSyntax.step true true w x y)) : Derives Γ (ProjectionTraceSyntax.tag w x y) := by
  apply Derives.disjE hy
  · exact selected_checked (ZFContext.add hZ _) w x y (add hw _) (.hyp (Or.inl rfl))
  · have hB : Derives (Context.add ((PairingProjectionSyntax.hasSelected true true w x).neg.conj (empty y)) Γ)
        ((PairingProjectionSyntax.hasSelected true true w x).neg.conj (empty y)) := .hyp (Or.inl rfl)
    have hz := PairingProjectionNatural.natural_raw_unselected_zero (ZFContext.add hZ _) true w x (add hw _) (add hx _) (.conjL hB)
    exact zero_checked (ZFContext.add hZ _) w x y (add hw _) hz (.conjR hB)

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.tag w x y)) :
    Derives Γ (PairingProjectionSyntax.step true true w x y) := by
  let B := (ProjectionTraceSyntax.tagRow w.castSucc x.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := condition_sound (ZFContext.under hZ B) w.castSucc x.castSucc y.castSucc (Fin.last m) hw1 (.conjL hB) (.conjR hB)
  exact of_eq (PairingProjectionSyntax.step_rename true true w x y Fin.castSucc).symm ho

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((ProjectionTraceSyntax.tag w x y).iff ((Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq : Derives (Context.add (ProjectionTraceSyntax.tag w x y) Γ) (ProjectionTraceSyntax.tag w x y) := .hyp (Or.inl rfl)
    exact .conjI (ProjectionNodeFields.tag_natural_at (ZFContext.add hZ _) w x y 0 (add hw _) hq)
      (checked_sound (ZFContext.add hZ _) w x y (add hw _) hq)
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y)) Γ)
        ((Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y)) := .hyp (Or.inl rfl)
    exact checked_complete (ZFContext.add hZ _) w x y (add hw _) (.conjL hB) (.conjR hB)

theorem checked_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (ProjectionTraceSyntax.tag w x y))
    (hz : Derives Γ (ProjectionTraceSyntax.tag w x z)) : Derives Γ (.equal y z) :=
  PairingProjection.functional_point hZ true true w x y z hw (checked_sound hZ w x y hw hy) (checked_sound hZ w x z hw hz)

end PPAC.Migration.Internal.ProjectionTag
