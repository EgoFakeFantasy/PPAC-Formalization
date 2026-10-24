import PPAC.Migration.Internal.InstantiateVariableSound
import PPAC.Migration.Internal.AbstractVariableComplete

/-! mode2独立数值分支实际重建原赋值、原头及闭轨迹；内部候选码不受外部标准性限制。 -/
namespace PPAC.Migration.Internal.InstantiateVariableComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax InstantiateVariableSound
open SyntaxRenameQuerySyntax (of_eq)
open AbstractVariableComplete (field_natural)
open YesMetaZFC.Automation.ObjectSyntaxTransform

theorem bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hlt : Derives Γ (.mem idx (xs 1))) (he : Derives Γ (.equal (xs 4) (xs 3))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => idx))
  have hi := SyntaxVariableDecode.index_natural true w idx (xs 3) hv
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hi (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 2) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hiGraph : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode false (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph true (.var 2) _ _ _ _ hiGraph hv
  have h4 := output_subst (varCode false (.var 2)) w (xs 3) (xs 4) env (eq_symm he) h3
  have hfields : ∀ j, Derives Γ (graph (boundIdentityFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 boundIdentityFields w r env xs hw hn hfields)) hc
  exact OriginalInstantiatePositive.bound_preserved hZ w r env hw hn hh hlt

theorem free_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (he : Derives Γ (.equal (xs 4) (xs 3))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => idx))
  have hi := SyntaxVariableDecode.index_natural false w idx (xs 3) hv
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hi (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 2) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hiGraph : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode true (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph false (.var 2) _ _ _ _ hiGraph hv
  have h4 := output_subst (varCode true (.var 2)) w (xs 3) (xs 4) env (eq_symm he) h3
  have hfields : ∀ j, Derives Γ (graph (freeIdentityFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 freeIdentityFields w r env xs hw hn hfields)) hc
  exact OriginalInstantiatePositive.free_identity hZ w r env hw hn hh

theorem bound_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hi : Derives Γ (.equal idx (xs 1))) (hy : Derives Γ (.equal (xs 4) (xs 2))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 2 → Fin m := SetLanguage.args2 (xs 1) (xs 2)
  have hn : Derives Γ (environmentNat 2 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (fun k => Fin.elim0 k)))
  have h0 : Derives Γ (graph (.literal 2) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hcidx := AbstractVariableIndex.code_index_subst true w idx (xs 1) (xs 3) hi hv
  have h3 := HornVariableExpr.code_graph true (.var 0) w (xs 1) (xs 3) env h1 hcidx
  have h4 : Derives Γ (graph (.var 1) w env (xs 4)) := .conjI (field_natural hZ w r xs hw hc 2) hy
  have hfields : ∀ j, Derives Γ (graph (boundPointFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun k => Fin.elim0 k)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 boundPointFields w r env xs hw hn hfields)) hc
  exact OriginalInstantiatePositive.bound_point hZ w r env hw hn hh

theorem bound_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx k : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hs : Derives Γ (successor idx k)) (hd : Derives Γ (.mem (xs 1) idx))
    (hy : Derives Γ (SyntaxVariableSyntax.code true w k (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => k))
  have hk := SyntaxVariableDecode.index_natural true w k (xs 4) hy
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hk (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 2) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hkGraph : Derives Γ (graph (.var 2) w env k) := .conjI hk (.eqRefl _)
  have hiGraph := intro_succ (.var 2) w idx k env hkGraph hs
  have h3 := HornVariableExpr.code_graph true (.succ (.var 2)) w idx (xs 3) env hiGraph hv
  have h4 := HornVariableExpr.code_graph true (.var 2) w k (xs 4) env hkGraph hy
  have hfields : ∀ j, Derives Γ (graph (boundPredecessorFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 boundPredecessorFields w r env xs hw hn hfields)) hc
  exact OriginalInstantiatePositive.bound_predecessor hZ w r idx env hw hn hh hs hd

theorem from_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ht : Derives Γ (InstantiateVariableValueSyntax.boundTail w (xs 1) idx (xs 4))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let B := (successor idx.castSucc (Fin.last m)).conj ((Formula.mem (xs 1).castSucc idx.castSucc).conj
    (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) (xs 4).castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 (xs 0) Fin.castSucc) (under hm B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_predecessor (ZFContext.under hZ B) w.castSucc r.castSucc idx.castSucc (Fin.last m)
    (fun j => (xs j).castSucc) hw1 hc1 hm1 hv1 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
  exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ho

end PPAC.Migration.Internal.InstantiateVariableComplete
