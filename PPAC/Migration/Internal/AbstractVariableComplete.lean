import PPAC.Migration.Internal.AbstractVariableSound

/-! 独立mode1变量数值分支实际重建原头图及闭轨迹，不预给赋值或解码轨迹。 -/
namespace PPAC.Migration.Internal.AbstractVariableComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax AbstractVariableSound
open YesMetaZFC.Automation.ObjectSyntaxTransform

theorem field_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (xs : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (i : Fin 5) :
    Derives Γ (.mem (xs i) w) :=
  StructuralListTraceOrder.member_member hZ w (xs i) r hw (SyntaxNodeInjective.constructor_range hZ 5 1 w xs r hw hc)
    (SyntaxConstructors.child_member hZ 5 1 w xs r i hw hc)

theorem bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hlt : Derives Γ (.mem idx (xs 1))) (he : Derives Γ (.equal (xs 4) (xs 3))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => idx))
  have hi := SyntaxVariableDecode.index_natural true w idx (xs 3) hv
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hi (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 1) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hiGraph : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode false (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph true (.var 2) _ _ _ _ hiGraph hv
  have h4 := output_subst (varCode false (.var 2)) w (xs 3) (xs 4) env (eq_symm he) h3
  have hfields : ∀ j, Derives Γ (graph (boundIdentityFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 boundIdentityFields w r env xs hw hn hfields)) hc
  exact OriginalAbstractPositive.bound_preserved hZ w r env hw hn hh hlt

theorem bound_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx s : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hs : Derives Γ (successor s idx)) (hlt : Derives Γ (.mem (xs 1) s)) (hy : Derives Γ (SyntaxVariableSyntax.code true w s (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => idx))
  have hi := SyntaxVariableDecode.index_natural true w idx (xs 3) hv
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hi (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 1) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hiGraph : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode false (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph true (.var 2) _ _ _ _ hiGraph hv
  have hsGraph := intro_succ (.var 2) w s idx env hiGraph hs
  have h4 := HornVariableExpr.code_graph true (.succ (.var 2)) w s (xs 4) env hsGraph hy
  have hfields : ∀ j, Derives Γ (graph (boundAbstractFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 boundAbstractFields w r env xs hw hn hfields)) hc
  exact OriginalAbstractPositive.bound_shifted hZ w r s env hw hn hh hs hlt

theorem free_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hz : Derives Γ (empty idx)) (hy : Derives Γ (SyntaxVariableSyntax.code true w (xs 1) (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 2 → Fin m := SetLanguage.args2 (xs 1) (xs 2)
  have hn : Derives Γ (environmentNat 2 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (fun z => Fin.elim0 z)))
  have h0 : Derives Γ (graph (.literal 1) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have h3 := HornVariableExpr.code_graph false (.literal 0) w idx (xs 3) env hz hv
  have h4 := HornVariableExpr.code_graph true (.var 0) w (xs 1) (xs 4) env h1 hy
  have hfields : ∀ j, Derives Γ (graph (freeHeadFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 freeHeadFields w r env xs hw hn hfields)) hc
  exact OriginalAbstractPositive.free_head hZ w r env hw hn hh

theorem free_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx k : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hs : Derives Γ (successor idx k)) (hy : Derives Γ (SyntaxVariableSyntax.code false w k (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env : Fin 3 → Fin m := Fin.cases (xs 1) (Fin.cases (xs 2) (fun _ => k))
  have hi := SyntaxVariableDecode.index_natural false w k (xs 4) hy
  have hn : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (Fin.cases (field_natural hZ w r xs hw hc 1) (Fin.cases (field_natural hZ w r xs hw hc 2) (Fin.cases hi (fun z => Fin.elim0 z))))
  have h0 : Derives Γ (graph (.literal 1) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (field_natural hZ w r xs hw hc 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (field_natural hZ w r xs hw hc 2) (.eqRefl _)
  have hk : Derives Γ (graph (.var 2) w env k) := .conjI hi (.eqRefl _)
  have hsGraph := intro_succ (.var 2) w idx k env hk hs
  have h3 := HornVariableExpr.code_graph false (.succ (.var 2)) w idx (xs 3) env hsGraph hv
  have h4 := HornVariableExpr.code_graph false (.var 2) w k (xs 4) env hk hy
  have hfields : ∀ j, Derives Γ (graph (freeTailFields j) w env (xs j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (fun z => Fin.elim0 z)))))
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 freeTailFields w r env xs hw hn hfields)) hc
  exact OriginalAbstractPositive.free_tail hZ w r env hw hn hh

end PPAC.Migration.Internal.AbstractVariableComplete
