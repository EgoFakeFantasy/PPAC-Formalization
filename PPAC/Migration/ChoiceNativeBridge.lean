import PPAC.Migration.ObjectGraphChoiceSelector

/-! 原Axioms.choice公式严格接合；仅本模块继承原choice闭性证书的额外既有依赖。 -/
namespace PPAC.Migration.ChoiceNativeBridge
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

theorem selector_ast : Translation.sentence ChoiceSyntax.selectorAC =
    Normalization.formula (Definitional.Project.fo_sentence Axioms.choice) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

theorem selector_equivalent {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Definitional.Project.fo_sentence Axioms.choice)
      (Translation.sentence ChoiceSyntax.selectorAC)) := by
  rw [selector_ast]
  exact Normalization.equivalent _

theorem to_native {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []}
    (h : FirstOrder.Derives T Γ (Translation.sentence ChoiceSyntax.selectorAC)) :
    FirstOrder.Derives T Γ (Definitional.Project.fo_sentence Axioms.choice) :=
  FirstOrder.Derives.iff_elim_right selector_equivalent h

theorem forward_kernel_certificate : FirstOrder.Derives (TheoryTransport.theory ObjectGraphChoiceSelector.assumptions) []
    (.imp AC (Definitional.Project.fo_sentence Axioms.choice)) := by
  apply FirstOrder.Derives.imp_intro
  apply to_native
  have hc : FirstOrder.Derives (TheoryTransport.theory ObjectGraphChoiceSelector.assumptions) []
      (.imp AC (Translation.sentence ChoiceSyntax.selectorAC)) := ObjectGraphChoiceSelector.forward_kernel_certificate
  exact FirstOrder.Derives.imp_elim hc.context_weaken_cons (FirstOrder.Derives.assumption List.mem_cons_self)

theorem native_forward : FirstOrder.Derives nativeZF [] (.imp AC (Definitional.Project.fo_sentence Axioms.choice)) :=
  ObjectGraphChoiceSelector.native_replay forward_kernel_certificate
end PPAC.Migration.ChoiceNativeBridge
