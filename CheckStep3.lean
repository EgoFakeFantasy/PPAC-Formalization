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
/-- 七条固定公理已经双向覆盖；新增两条均为对象原核推导。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.infinity) := ZFEquivalence.source_infinity
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.foundation) := ZFEquivalence.source_foundation
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity) := ZFEquivalence.native_infinity
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation) := ZFEquivalence.native_foundation

/-- 全分离模式，不限制参数个数和矩阵复杂度。 -/
theorem separation_source_to_native {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.separation p)) :=
  SeparationSyntax.source_separation p

theorem separation_native_of_source_matrix {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence
        (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p))) :=
  SeparationSyntax.native_separation_of_source_matrix p

/-- 多个参数和内嵌混合量词的实例也走同一个全模式定理。 -/
def parameterMatrix : Source.Formula 4 :=
  .all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 4 3).imp (.equal 1 2))))
example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.separation parameterMatrix)) :=
  SeparationSyntax.source_separation parameterMatrix
/-- 任意原生矩阵的反向分离模式，不再只限于ProjectSyntax.unary p。 -/
theorem arbitrary_native_separation {n} (s : SetTheory.Definitional.Project.UnarySchema n) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation s)) :=
  SeparationReverse.native_separation s

def projectMatrix : SetTheory.Definitional.Project.UnarySchema 2 where
  body := .iff .truth (.forallE (.imp
    (SetTheory.Definitional.Project.Formula.subset (.bound 0) (.bound 1))
    (.neg (SetTheory.Definitional.Project.Formula.extensionalEq (.bound 2) (.bound 3)))))
  freeClosed := by simp [SetTheory.Definitional.Formula.FreeClosed]

/-- 子集原子、独立连接词、多个参数和量词同时出现的实际原核回放。 -/
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation projectMatrix)) :=
  SeparationReverse.native_separation projectMatrix

/-- 全参数Collection的源呈现只从原Collection版ZF取得，没有假定源ZF已经证明它。 -/
theorem collection_source_presentation {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (CollectionSyntax.collection p)) :=
  CollectionSyntax.source_collection p

theorem arbitrary_collection_roundtrip {n} (s : SetTheory.Definitional.Project.BinarySchema n) :
    FirstOrder.Derives noAxioms [] (.iff
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.collection s))
      (Translation.sentence (CollectionSyntax.collection (ProjectDecode.reverse s.body s.freeClosed)))) :=
  CollectionSyntax.native_collection_equivalent s
/-- 任意参数及任意矩阵的原始Replacement句子，实际在原Collection版ZF内推导。 -/
theorem all_source_replacement {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.native_replacement p

/-- 两模式实例的原核证书与原ZF回放分开验收，防止循环假定Replacement。 -/
theorem replacement_two_instances {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives (TheoryTransport.theory (ReplacementFromCollection.assumptions p)) []
      (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.kernel_certificate p

theorem source_ZF_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.ZF.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) := ZFReplay.source_closed_at h

theorem source_target_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.targetTheory.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives targetTheory [] (Translation.sentence p) := ZFReplay.source_target_closed_at h

/-- 实际源Replacement公理证书经完整源ZF接口回放；不再停留在未对应的理论像。 -/
theorem replay_replacement_through_source_ZF {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) := by
  apply ZFReplay.source_closed_at (n := 1)
  exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement p, rfl⟩

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement (Source.Formula.equal 0 1 : Source.Formula 2))) :=
  ReplacementFromCollection.native_replacement _

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement
      (Source.Formula.all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 3 4).imp (.equal 1 2)))) : Source.Formula 4))) :=
  ReplacementFromCollection.native_replacement _
end PPAC.Migration.Step3Checks
