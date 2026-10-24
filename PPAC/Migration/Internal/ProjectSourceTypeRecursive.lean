import PPAC.Migration.Internal.ProjectSourceTypeLocalTransfer

/-! 全部内部候选码/上下文上的历史无关完整类型递归式；非自然分支也正式处理。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PowerSetSyntax ProjectSourceTypeRecursionSyntax ProjectSourceTypeStateSyntax ProjectSourceTypeEvaluationSyntax ProjectSourceTypeJudgmentSyntax ProjectSourceTypeRecursiveSyntax ProjectSourceTypeLocalTransfer
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c b f h n v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a))
    (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n)) (hs : Derives Γ (state w c n h v)) :
    Derives Γ ((edge v b f).iff (criterion w c n b f)) := by
  have hh := iff_trans (ProjectSourceTypeStateMembership.edge_iff hZ w a c n h v b f ha hc hs)
    (all_iff hZ w c b f h n hw hn hg)
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (add hn _) (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjR (.hyp (Or.inl rfl)))

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n v b f : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a))
    (hn : Derives Γ (.mem n w)) (hv : Derives Γ (evaluation w c n v)) :
    Derives Γ ((typed w c n b f).iff (criterion w c n b f)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have hh := ProjectSourceTypeHistory.from_value hZ w c n v ho hv
  let H := (graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have hZ1 := ZFContext.under hZ H
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw H
  have ha1 : Derives Δ (powerOf a.castSucc w.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under ha H
  have hc1 : Derives Δ (powerOf c.castSucc a.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under hc H
  have ho1 : Derives Δ (OrdinalSyntax.ordinal n.castSucc) := by simpa only [Formula.raise, OrdinalSyntax.ordinal_rename] using under ho H
  have hv1 : Derives Δ (evaluation w.castSucc c.castSucc n.castSucc v.castSucc) := by
    simpa only [Formula.raise, evaluation_rename] using under hv H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ht := ProjectSourceTypeJudgment.at_value hZ1 w.castSucc c.castSucc n.castSucc b.castSucc f.castSucc v.castSucc ho1 (under hn H) hv1
  have hs := at_state hZ1 w.castSucc a.castSucc c.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc v.castSucc hw1 ha1 hc1 (under hn H) (.conjL hH) (.conjR hH)
  have hout := iff_trans ht hs
  simpa only [Formula.raise, Formula.iff, Formula.rename, typed_rename, criterion_rename] using hout

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a)) :
    Derives Γ ((typed w c n b f).iff (criterion w c n b f)) := by
  apply SourcePropositional.by_cases (Formula.mem n w)
  · let N := Formula.mem n w
    let Ξ := Context.add N Γ
    have hn : Derives Ξ N := .hyp (Or.inl rfl)
    have he := ProjectSourceTypeEvaluationExistence.at_natural (ZFContext.add hZ N) w c n (add hw N) hn
    let V := evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) he
    have hZ1 := ZFContext.under (ZFContext.add hZ N) V
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw N) V
    have ha1 : Derives Δ (powerOf a.castSucc w.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under (add ha N) V
    have hc1 : Derives Δ (powerOf c.castSucc a.castSucc) := by simpa only [Formula.raise, powerOf_rename] using under (add hc N) V
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have hout := at_value hZ1 w.castSucc a.castSucc c.castSucc n.castSucc (Fin.last m) b.castSucc f.castSucc
      hw1 ha1 hc1 (under hn V) hV
    simpa only [Formula.raise, Formula.iff, Formula.rename, typed_rename, criterion_rename] using hout
  · apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))
end PPAC.Migration.Internal.ProjectSourceTypeRecursive
