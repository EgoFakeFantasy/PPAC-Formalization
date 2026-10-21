import PPAC

/-! 反向句法的对象核回放；不宣称Replacement/Collection或两种AC已等价。 -/
namespace PPAC.Migration.Step3Checks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev noAxioms : FirstOrder.Theory ℒ := fun _ => False

def binders : FirstOrder.Sentence ℒ :=
  .forallE .set (.existsE .set (.neg
    (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))))

/-- 原生首变量绑定严格变成源末变量绑定。 -/
example : Reverse.sentence binders = .all (.ex ((Source.Formula.mem 0 1).neg)) := rfl

/-- 原生独立连接词展开成源8构造器，无真值谓词或新符号。 -/
example : Reverse.sentence (.iff .truth (.neg .falsum)) =
    (Source.Formula.imp .bot .bot).iff (.imp .bot .bot) := rfl

/-- 嵌套混合量词的等价是实际对象推导，而不是Realize定理。 -/
theorem binder_roundtrip : FirstOrder.Derives noAxioms []
    (.iff binders (Translation.sentence (Reverse.sentence binders))) :=
  Reverse.sentence_equivalent binders

def allConnectives : FirstOrder.Sentence ℒ :=
  .conj (.iff .truth (.imp .falsum .falsum))
    (.forallE .set (.disj (.equal (.bvar .here) (.bvar .here))
      (.existsE .set (.neg (.equal (.bvar .here) (.bvar (.there .here)))))))

theorem all_connectives_roundtrip : FirstOrder.Derives noAxioms []
    (.iff allConnectives (Translation.sentence (Reverse.sentence allConnectives))) :=
  Reverse.sentence_equivalent allConnectives

example : Reverse.sentence (Translation.sentence Source.SetLanguage.PP) = Source.SetLanguage.PP :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.AC) = Source.SetLanguage.AC :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.ACwo) = Source.SetLanguage.ACwo :=
  Reverse.source_sentence_roundtrip _

/-- 任意参数个数和任意矩阵，非有限样本。 -/
theorem replacement_roundtrip {n} (p : Source.Formula (n+2)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.replacement p)) =
      Source.SetLanguage.replacement p := Reverse.source_sentence_roundtrip _

theorem separation_roundtrip {n} (p : Source.Formula (n+1)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.separation p)) =
      Source.SetLanguage.separation p := Reverse.source_sentence_roundtrip _

/-- 任意理论和开放推导均可在规范化公理呈现间回放。 -/
theorem presentation_replay {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives T Γ p) :
    FirstOrder.Derives (Presentation.theory T) Γ p := Presentation.derives_iff.mpr h

theorem native_ZF_presentation {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives (Presentation.theory nativeZF) Γ p ↔
      FirstOrder.Derives nativeZF Γ p := Presentation.derives_iff

/-- 原生外延公理的规范化确实落在source语法像；不等同于源ZF呈现等价。 -/
theorem native_extensionality_replay :
    FirstOrder.Derives (Presentation.theory nativeZF) []
      (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := by
  apply Presentation.replay_original_axiom
  exact ⟨_, SetTheory.ZF.Axiom.extensionality, rfl⟩

/-- 五条已对齐公理，验收源→原生、原生→源句子像两个方向。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.extensionality) :=
  ZFEquivalence.source_extensionality
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.emptySet) :=
  ZFEquivalence.source_emptySet
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.pairing) :=
  ZFEquivalence.source_pairing
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.union) :=
  ZFEquivalence.source_union
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.powerSet) :=
  ZFEquivalence.source_powerSet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := ZFEquivalence.native_extensionality
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.emptySet) := ZFEquivalence.native_emptySet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.pairing) := ZFEquivalence.native_pairing
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.union) := ZFEquivalence.native_union
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.powerSet) := ZFEquivalence.native_powerSet
end PPAC.Migration.Step3Checks
