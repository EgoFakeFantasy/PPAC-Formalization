import PPAC.Migration.CollectionFromReplacement
import PPAC.Migration.ReverseDerivation

/-! 原Collection版ZF与源Replacement版ZF的完整双向实际推导回放；内部码表示仍另行证明。 -/
namespace PPAC.Migration.ReverseZFReplay
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

theorem replay_project_axiom {q : Definitional.Project.Sentence} (hq : SetTheory.ZF q) :
    FirstOrder.Derives ZFEquivalence.sourceZF [] (Definitional.Project.fo_sentence q) := by
  cases hq with
  | extensionality => exact ZFEquivalence.native_extensionality
  | emptySet => exact ZFEquivalence.native_emptySet
  | pairing => exact ZFEquivalence.native_pairing
  | union => exact ZFEquivalence.native_union
  | powerSet => exact ZFEquivalence.native_powerSet
  | infinity => exact ZFEquivalence.native_infinity
  | foundation => exact ZFEquivalence.native_foundation
  | separation p => exact SeparationReverse.native_separation p
  | collection p => exact CollectionFromReplacement.native_project_matrix p

theorem replay_axiom {q : FirstOrder.Sentence ℒ} (hq : nativeZF q) :
    FirstOrder.Derives ZFEquivalence.sourceZF [] q := by
  rcases hq with ⟨p, hp, rfl⟩
  exact replay_project_axiom hp

/-- 全部内部语言的任意开放原核推导，保留自由上下文和局部假设。 -/
theorem replay {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives nativeZF Γ p) : FirstOrder.Derives ZFEquivalence.sourceZF Γ p :=
  FirstOrder.Derives.theory_cut (fun hq => replay_axiom hq) h

theorem derives_iff {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives nativeZF Γ p ↔ FirstOrder.Derives ZFEquivalence.sourceZF Γ p :=
  ⟨replay, ZFReplay.replay⟩

/-- 任意原核闭句实际返回源19规则，使用一个未用外部变量。 -/
theorem source_native_sentence {p : FirstOrder.Sentence ℒ} (h : FirstOrder.Derives nativeZF [] p) :
    Source.Derives (Source.SetLanguage.ZF.at 1) ((Reverse.sentence p).rename Fin.elim0) := by
  have hc := ReverseCompile.sentence (replay h)
  rw [ZFEquivalence.sourceZF, ReverseCompile.source_theory_roundtrip] at hc
  exact hc

theorem source_sentence {p : Source.Sentence} (h : FirstOrder.Derives nativeZF [] (Translation.sentence p)) :
    Source.Derives (Source.SetLanguage.ZF.at 1) (p.rename Fin.elim0) :=
  ReverseCompile.source_sentence (replay h)

/-- 闭句往返是外部证书编译接口，不能当成内部Proof/Con正确性。 -/
theorem source_sentence_iff {p : Source.Sentence} :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) ↔
      Source.Derives (Source.SetLanguage.ZF.at 1) (p.rename Fin.elim0) :=
  ⟨source_sentence, ZFReplay.source_closed_at⟩

/-- 目标附加三句仍严格使用原PP/ACwo/非AC图公式。 -/
theorem target_axiom {q : FirstOrder.Sentence ℒ} (hq : targetTheory q) :
    FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.targetTheory) [] q := by
  rcases hq with h | rfl | rfl | rfl
  · exact (replay_axiom h).theory_weaken (by
      rintro p ⟨s, hs, rfl⟩
      exact ⟨s, Or.inl hs, rfl⟩)
  · simpa [PP, FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
      (FirstOrder.Derives.theory_axiom (T := TheoryTransport.theory Source.SetLanguage.targetTheory) (free := [])
        ⟨Source.SetLanguage.PP, Or.inr (Or.inl rfl), rfl⟩)
  · simpa [ACwo, FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
      (FirstOrder.Derives.theory_axiom (T := TheoryTransport.theory Source.SetLanguage.targetTheory) (free := [])
        ⟨Source.SetLanguage.ACwo, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
  · simpa [notAC, FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
      (FirstOrder.Derives.theory_axiom (T := TheoryTransport.theory Source.SetLanguage.targetTheory) (free := [])
        ⟨Source.SetLanguage.AC.neg, Or.inr (Or.inr (Or.inr rfl)), rfl⟩)

theorem target_replay {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives targetTheory Γ p) :
    FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.targetTheory) Γ p :=
  FirstOrder.Derives.theory_cut (fun hq => target_axiom hq) h

theorem target_derives_iff {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives targetTheory Γ p ↔
      FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.targetTheory) Γ p :=
  ⟨target_replay, ZFReplay.target_replay⟩

theorem source_target_sentence {p : Source.Sentence} (h : FirstOrder.Derives targetTheory [] (Translation.sentence p)) :
    Source.Derives (Source.SetLanguage.targetTheory.at 1) (p.rename Fin.elim0) :=
  ReverseCompile.source_sentence (target_replay h)

theorem source_target_sentence_iff {p : Source.Sentence} :
    FirstOrder.Derives targetTheory [] (Translation.sentence p) ↔
      Source.Derives (Source.SetLanguage.targetTheory.at 1) (p.rename Fin.elim0) :=
  ⟨source_target_sentence, ZFReplay.source_target_closed_at⟩
end PPAC.Migration.ReverseZFReplay
