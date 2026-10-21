import PPAC.Migration.Internal.SyntaxTypeRecursiveSyntax

/-! 在严格子码处把真实Read迁移为Typed，包括所有内部后继bound见证。 -/
namespace PPAC.Migration.Internal.SyntaxTypeReadTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax OrdinalSyntax SyntaxTypeRecursionSyntax SyntaxContextReadSyntax SyntaxTypeJudgmentSyntax SyntaxTypeRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem plain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c h n x b f : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hx : Derives Γ (.mem x n))
    (hg : Derives Γ (graph w c h n)) : Derives Γ ((read h x b f).iff (typed w c x b f)) :=
  SyntaxTypeJudgment.read_iff hZ w c h n x b f (NaturalOrderBasic.ordinal hZ w n hw hn) hx
    (StructuralListTraceOrder.member_member hZ w x n hw hn hx) hg

theorem advanced {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c h n x b f : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hx : Derives Γ (.mem x n))
    (hg : Derives Γ (graph w c h n)) :
    Derives Γ ((SyntaxContextReadSyntax.advanced h x b f).iff (advancedTyped w c x b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := SyntaxContextReadSyntax.advanced h x b f
    let Ξ := Context.add P Γ
    let K := (successor (Fin.last m) b.castSucc).conj (read h.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Δ := Context.add K (Context.image Formula.raise Ξ)
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) K
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) K
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc n.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg P) K
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have hh := plain hZ1 w.castSucc c.castSucc h.castSucc n.castSucc x.castSucc (Fin.last m) f.castSucc
      hw1 (under (add hn P) K) (under (add hx P) K) hg1
    have ht := Derives.impE (.conjL hh) (.conjR hK)
    have hout := SyntaxTypeRecursiveSyntax.intro_advanced _ _ _ _ _ (Fin.last m) (.conjL hK) ht
    simpa only [Formula.raise, advancedTyped_rename] using hout
  · apply Derives.impI
    let P := advancedTyped w c x b f
    let Ξ := Context.add P Γ
    let K := (successor (Fin.last m) b.castSucc).conj (typed w.castSucc c.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Δ := Context.add K (Context.image Formula.raise Ξ)
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) K
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) K
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc n.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg P) K
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have hh := plain hZ1 w.castSucc c.castSucc h.castSucc n.castSucc x.castSucc (Fin.last m) f.castSucc
      hw1 (under (add hn P) K) (under (add hx P) K) hg1
    have hr := Derives.impE (.conjR hh) (.conjR hK)
    have hout := SyntaxContextReadSyntax.intro_advanced _ _ _ _ (Fin.last m) (.conjL hK) hr
    simpa only [Formula.raise, advanced_rename] using hout

theorem check_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w c h n x b f : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hx : Derives Γ (.mem x n))
    (hg : Derives Γ (graph w c h n)) :
    Derives Γ ((check advance h x b f).iff (stepCheck advance w c x b f)) := by
  cases advance with
  | false => exact plain hZ w c h n x b f hw hn hx hg
  | true => exact advanced hZ w c h n x b f hw hn hx hg
end PPAC.Migration.Internal.SyntaxTypeReadTransfer
