import PPAC.Migration.ReplacementFromCollection

/-! 完整源ZF与源目标理论的正向原核回放。Collection的反向推导和内部Con仍另行证明。 -/
namespace PPAC.Migration.ZFReplay
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

theorem replay_axiom {s : Source.Sentence} (h : Source.SetLanguage.ZF s) :
    FirstOrder.Derives nativeZF [] (Translation.sentence s) := by
  cases h with
  | extensionality => exact ZFEquivalence.source_extensionality
  | emptySet => exact ZFEquivalence.source_emptySet
  | pairing => exact ZFEquivalence.source_pairing
  | union => exact ZFEquivalence.source_union
  | powerSet => exact ZFEquivalence.source_powerSet
  | infinity => exact ZFEquivalence.source_infinity
  | foundation => exact ZFEquivalence.source_foundation
  | separation p => exact SeparationSyntax.source_separation p
  | replacement p => exact ReplacementFromCollection.native_replacement p

/-- 原核中源ZF句子像的任何开放推导，回放到真正的原Collection版ZF。 -/
theorem replay {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives ZFEquivalence.sourceZF Γ p) : FirstOrder.Derives nativeZF Γ p := by
  apply FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, rfl⟩
  exact replay_axiom hs

theorem source_derives_at {n} {p : Source.Formula n}
    (h : Source.Derives (Source.SetLanguage.ZF.at n) p)
    {free : Syntax.Ctx} (ρ : Fin n → Syntax.Tm [] free) :
    FirstOrder.Derives nativeZF [] (Syntax.formula ρ p) := replay (TheoryTransport.derives_at h ρ)

theorem source_closed_at {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.ZF.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) := replay (TheoryTransport.closed_at h)

/-- 外部一致性方向，仅是已证编译器的推论；不是内部Con对象定理。 -/
theorem consistent_source_of_native (h : Consistent nativeZF) : Source.Consistent Source.SetLanguage.ZF := by
  apply TheoryTransport.consistent_source_of_native
  intro d
  exact h (replay d)

theorem target_axiom {s : Source.Sentence} (h : Source.SetLanguage.targetTheory s) :
    FirstOrder.Derives targetTheory [] (Translation.sentence s) := by
  rcases h with h | rfl | rfl | rfl
  · exact (replay_axiom h).theory_weaken (fun hq => Or.inl hq)
  · exact target_derives_PP
  · exact target_derives_ACwo
  · exact target_derives_source_notAC

theorem target_replay {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.targetTheory) Γ p) :
    FirstOrder.Derives targetTheory Γ p := by
  apply FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, rfl⟩
  exact target_axiom hs

theorem source_target_derives_at {n} {p : Source.Formula n}
    (h : Source.Derives (Source.SetLanguage.targetTheory.at n) p)
    {free : Syntax.Ctx} (ρ : Fin n → Syntax.Tm [] free) :
    FirstOrder.Derives targetTheory [] (Syntax.formula ρ p) :=
  target_replay (TheoryTransport.derives_at h ρ)

theorem source_target_closed_at {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.targetTheory.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives targetTheory [] (Translation.sentence p) := target_replay (TheoryTransport.closed_at h)
end PPAC.Migration.ZFReplay
