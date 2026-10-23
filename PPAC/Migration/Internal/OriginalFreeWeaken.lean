import PPAC.Migration.Internal.OriginalFreeWeakenSound
import PPAC.Migration.Internal.HornLookupPowerCondition

/-! 原模式0自由变量：完整原轨迹与实际后继变量值双向对应。 -/
namespace PPAC.Migration.Internal.OriginalFreeWeaken
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (freeWeaken varCode)

theorem trace_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (FreeWeakenValueSyntax.shifted w idx (xs 4)) := by
  let B := HornLookupConditionSyntax.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w.castSucc (fun i => (xs i).castSucc) r.castSucc) := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (xs 0).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc (xs 3).castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := OriginalVariableDispatch.closed_member_application hZ1 false false _ _ _ _ _ hw1 hc1 hm1 hv1 (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ho := OriginalFreeWeakenSound.application_shifted hZ1 _ _ _ _ _ hw1 hc1 hv1 ha
  exact of_eq (FreeWeakenValueSyntax.shifted_rename w idx (xs 4) Fin.castSucc).symm ho

theorem shifted_trace {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (he : Derives Γ (FreeWeakenValueSyntax.shifted w idx (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let B := (successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) (xs 4).castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w.castSucc (fun i => (xs i).castSucc) r.castSucc) := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (xs 0).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc (xs 3).castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let env := OriginalLookupExpr.rowFields (xs 1).castSucc (xs 2).castSucc idx.castSucc
  have hr := SyntaxNodeInjective.constructor_range hZ1 5 1 _ _ _ hw1 hc1
  have hn (i : Fin 5) : Derives Δ (.mem (xs i).castSucc w.castSucc) := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 hr (SyntaxConstructors.child_member hZ1 5 1 _ _ _ i hw1 hc1)
  have hi := SyntaxVariableDecode.index_natural false _ _ _ hv1
  have henv : Derives Δ (environmentNat 3 w.castSucc env) := HornApplicationRules.intro_nat _ env
    (fun i => Fin.cases (hn 1) (fun j => Fin.cases (hn 2) (fun k => Fin.cases hi (fun z => Fin.elim0 z) k) j) i)
  have h0 : Derives Δ (graph (.literal 0) w.castSucc env (xs 0).castSucc) := hm1
  have h1 : Derives Δ (graph (.var 0) w.castSucc env (xs 1).castSucc) := .conjI (hn 1) (.eqRefl _)
  have h2 : Derives Δ (graph (.var 1) w.castSucc env (xs 2).castSucc) := .conjI (hn 2) (.eqRefl _)
  have hx : Derives Δ (graph (.var 2) w.castSucc env idx.castSucc) := .conjI hi (.eqRefl _)
  have h3 : Derives Δ (graph (varCode true (.var 2)) w.castSucc env (xs 3).castSucc) := HornVariableExpr.code_graph false (.var 2) _ _ _ _ hx hv1
  have hsgraph := intro_succ (.var 2) _ _ _ _ hx (.conjL hB)
  have h4 : Derives Δ (graph (varCode true (.succ (.var 2))) w.castSucc env (xs 4).castSucc) := HornVariableExpr.code_graph false (.succ (.var 2)) _ _ _ _ hsgraph (.conjR hB)
  have hs : ∀ i, Derives Δ (graph (OriginalFreeWeakenSound.fields i) w.castSucc env (xs i).castSucc) :=
    fun i => Fin.cases h0 (fun a => Fin.cases h1 (fun b => Fin.cases h2 (fun c => Fin.cases h3 (fun d => Fin.cases h4 (fun z => Fin.elim0 z) d) c) b) a) i
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ1 5 1 OriginalFreeWeakenSound.fields _ _ env _ hw1 henv hs)) hc1
  have ho := OriginalScalarPositive.free_zero hZ1 _ _ env hw1 henv hh
  exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ho

theorem trace_iff_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (FreeWeakenValueSyntax.shifted w idx (xs 4))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact trace_shifted (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact shifted_trace (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

theorem power_trace_iff_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupPowerCondition.condition w r).iff (FreeWeakenValueSyntax.shifted w idx (xs 4))) := by
  have hs := HornLookupSearchCondition.condition_iff hZ w r hw
  have hp := HornLookupPowerCondition.search_condition_iff hZ w r
  exact SyntaxTypeLocalTransfer.iff_trans hp (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hs) (.conjL hs)) (trace_iff_shifted hZ w r idx xs hw hc hm hv))

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).neg.iff (FreeWeakenValueSyntax.shifted w idx (xs 4)).neg) :=
  FormulaTransformCongruence.imp_congr (trace_iff_shifted hZ w r idx xs hw hc hm hv) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.OriginalFreeWeaken
