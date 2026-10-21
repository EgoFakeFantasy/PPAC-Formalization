import PPAC.Migration.ObjectSelectorGraphChoice

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

theorem reverse_kernel_certificate : FirstOrder.Derives (TheoryTransport.theory ObjectSelectorGraphChoice.assumptions) []
    (.imp (Definitional.Project.fo_sentence Axioms.choice) AC) := by
  apply FirstOrder.Derives.imp_intro
  have hc : FirstOrder.Derives (TheoryTransport.theory ObjectSelectorGraphChoice.assumptions) []
      (.imp (Translation.sentence ChoiceSyntax.selectorAC) AC) := ObjectSelectorGraphChoice.reverse_kernel_certificate
  have hs : FirstOrder.Derives (TheoryTransport.theory ObjectSelectorGraphChoice.assumptions)
      [Definitional.Project.fo_sentence Axioms.choice] (Translation.sentence ChoiceSyntax.selectorAC) :=
    FirstOrder.Derives.iff_elim_left selector_equivalent (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.imp_elim hc.context_weaken_cons hs

theorem native_reverse : FirstOrder.Derives nativeZF [] (.imp (Definitional.Project.fo_sentence Axioms.choice) AC) :=
  ObjectSelectorGraphChoice.native_replay reverse_kernel_certificate

theorem native_equivalence : FirstOrder.Derives nativeZF [] (.iff AC (Definitional.Project.fo_sentence Axioms.choice)) := by
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim native_forward.context_weaken_cons (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.imp_elim native_reverse.context_weaken_cons (FirstOrder.Derives.assumption List.mem_cons_self)
end PPAC.Migration.ChoiceNativeBridge
