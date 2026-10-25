import PPAC.Migration.ZFEquivalence
import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserSchedule
import YesMetaZFC.Model.Henkin.StrongCompleteness
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
/-! Reuse the existing Project semantics and the same original-kernel closing
interface used by BMS. The background here is ZF with full Separation and
Collection. No ZFC model or externally well-founded model is assumed.
Completeness still requires truth in every corresponding Type 0 model;
a theorem about a single concrete model does not supply that premise. -/
namespace PPAC.Migration.ModelTransfer
attribute [local implicit_reducible] SetTheory.signature
universe x
variable {M : FirstOrder.Structure.{0,0,0,x} ℒ}
/-- Obtain extensionality from the already accepted source axiom transfer. -/
theorem extensionality (hM : FirstOrder.Theory.Models M nativeZF) :
    SetTheory.Extensional (Definitional.Project.FirstOrderSemantics.reduct M) := by
  have h := (Translation.realizes_sentence M Source.SetLanguage.extensionality).mp
    (ZFEquivalence.source_extensionality.semantically_entails M hM)
  constructor
  intro left right hSame
  exact h left right (fun element => ⟨(hSame element).mp, (hSame element).mpr⟩)
/-- Reuse the generic model bridge for the exact original ZF theory. -/
theorem project_models_iff :
    FirstOrder.Theory.Models M nativeZF ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).Models SetTheory.ZF := by
  constructor
  · intro hM
    exact (Definitional.Project.FirstOrderSemantics.models_iff (extensionality hM) SetTheory.ZF).mp hM
  · intro hM
    exact (Definitional.Project.FirstOrderSemantics.models_iff hM.1 SetTheory.ZF).mpr hM

/-- Existing pure-language schedule; arbitrary theory, original Derives kernel. -/
theorem derives {T : FirstOrder.Theory ℒ} {φ : FirstOrder.Sentence ℒ}
    (h : FirstOrder.Theory.SemanticallyEntails.{0,0,0,0} T φ) :
    FirstOrder.Derives T [] φ :=
  FirstOrder.Completeness.strong_completeness
    FirstOrder.FormalSystem.ProofT.ZFC.PureRosserSchedule.target h

/-- Consume existing Project mathematics only after proving the all-model premise. -/
theorem project_derives (φ : Definitional.Project.Sentence)
    (h : ∀ N : SetTheory.Structure.{0}, N.Models SetTheory.ZF → N.SatisfiesSentence φ) :
    FirstOrder.Derives nativeZF [] (Definitional.Project.fo_sentence φ) := by
  apply derives
  intro M hM
  exact (Definitional.Project.FirstOrderSemantics.sentence_correct (extensionality hM) φ).mpr
    (h _ (project_models_iff.mp hM))

/-- The additional U axioms are the actual translated closed sentences. -/
theorem target_models_iff : FirstOrder.Theory.Models M targetTheory ↔
    FirstOrder.Theory.Models M nativeZF ∧
    (Translation.sentence Source.SetLanguage.PP).TrueIn M ∧
    (Translation.sentence Source.SetLanguage.ACwo).TrueIn M ∧
    ¬ (Translation.sentence Source.SetLanguage.AC).TrueIn M := by
  constructor
  · intro hM
    refine ⟨(fun p hp => hM p (Or.inl hp)), target_derives_PP.semantically_entails M hM,
      target_derives_ACwo.semantically_entails M hM, ?_⟩
    exact target_derives_notAC.semantically_entails M hM
  · rintro ⟨hZF, hPP, hWO, hAC⟩ p hp
    rcases hp with hp | rfl | rfl | rfl
    · exact hZF _ hp
    · exact hPP
    · exact hWO
    · exact hAC
/-- Exact source-matrix/Project-model interface, in every model universe. -/
theorem target_project_models_iff : FirstOrder.Theory.Models M targetTheory ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).Models SetTheory.ZF ∧
    Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem Fin.elim0 Source.SetLanguage.PP ∧
    Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem Fin.elim0 Source.SetLanguage.ACwo ∧
    ¬ Source.Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem Fin.elim0 Source.SetLanguage.AC := by
  rw [target_models_iff, project_models_iff]
  simp only [FirstOrder.Formula.TrueIn, Translation.realizes_sentence]
  rfl
end PPAC.Migration.ModelTransfer
