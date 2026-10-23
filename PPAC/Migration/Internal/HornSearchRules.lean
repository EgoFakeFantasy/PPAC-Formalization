import PPAC.Migration.Internal.HornSearchSyntax

/-! 不增加输入前提的原后继有界搜索接口：实际取得界值并回放完整原规则表。 -/
namespace PPAC.Migration.Internal.HornSearchRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornStepSyntax HornSearchSyntax HornApplicationBounds
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem step_iff_bounded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rules : List Rule) (w row trace s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) (hs : Derives Γ (successor s row)) :
    Derives Γ ((step rules w row trace).iff (boundedStep rules w row trace s)) := by
  induction rules with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl .bot
  | cons rule rules ih => exact SyntaxTypeLocalTransfer.disj_congr (application_iff_boundedAt hZ rule w row trace s hw hr hs) ih

theorem step_iff_search {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rules : List Rule) (w row trace : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem row w)) :
    Derives Γ ((step rules w row trace).iff (searchStep rules w row trace)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := step rules w row trace
    have he := InsertExistence.exists_insert row row (ZFContext.arithmetic (ZFContext.add hZ E)).base.pairing (ZFContext.arithmetic (ZFContext.add hZ E)).base.union
    let S := successor (Fin.last m) row.castSucc
    let Δ := Context.add S (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := S) he
    have hZ1 := ZFContext.under (ZFContext.add hZ E) S
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) S)
    have hr1 : Derives Δ (.mem row.castSucc w.castSucc) := under (add hr E) S
    have he1 : Derives Δ (step rules w.castSucc row.castSucc trace.castSucc) := of_eq (step_rename rules w row trace Fin.castSucc)
      (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) S)
    have hS : Derives Δ S := .hyp (Or.inl rfl)
    have ho := intro_search rules _ _ _ _ hS (.impE (.conjL (step_iff_bounded hZ1 rules _ _ _ _ hw1 hr1 hS)) he1)
    exact of_eq (searchStep_rename rules w row trace Fin.castSucc).symm ho
  · apply Derives.impI
    let E := searchStep rules w row trace
    let B := searchBody rules w row trace
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hr1 : Derives Δ (.mem row.castSucc w.castSucc) := under (add hr E) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjR (step_iff_bounded hZ1 rules _ _ _ _ hw1 hr1 (.conjL hB))) (.conjR hB)
    exact of_eq (step_rename rules w row trace Fin.castSucc).symm ho

theorem original_search_iff_lookup {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w row trace : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k 0 w xs row)) :
    Derives Γ ((originalSearchStep w row trace).iff (lookupStep w row trace)) := by
  have hr := SyntaxNodeInjective.constructor_range hZ k 0 w xs row hw hc
  have he := step_iff_search hZ YesMetaZFC.Automation.ObjectSyntaxTransform.rules w row trace hw hr
  exact SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR he) (.conjL he)) (OriginalLookupDispatch.dispatch_iff hZ k w row trace xs hw hc)

end PPAC.Migration.Internal.HornSearchRules
