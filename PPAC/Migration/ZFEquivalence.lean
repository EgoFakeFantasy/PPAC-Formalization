import PPAC.Migration.Contract
import PPAC.Migration.Presentation
import PPAC.Migration.SourceTheory

/-! 源Replacement版ZF与原Collection版ZF的对应：本模块目前只完成五条固定公理。
无穷/基础的逻辑重排、两种全模式仍待证明；不得把本模块名当作完整ZF等价。 -/
namespace PPAC.Migration.ZFEquivalence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

def sourceZF : FirstOrder.Theory ℒ := TheoryTransport.theory Source.SetLanguage.ZF

theorem extensionality_ast : Translation.sentence Source.SetLanguage.extensionality =
    Normalization.formula (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

theorem emptySet_ast : Translation.sentence Source.SetLanguage.emptySet =
    Normalization.formula (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.emptySet) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

theorem pairing_ast : Translation.sentence Source.SetLanguage.pairing =
    Normalization.formula (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.pairing) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

theorem union_ast : Translation.sentence Source.SetLanguage.union =
    Normalization.formula (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.union) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

theorem powerSet_ast : Translation.sentence Source.SetLanguage.powerSet =
    Normalization.formula (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.powerSet) := by
  rw [← Reverse.native_sentence_roundtrip]
  congr 1
  decide +kernel

/-- 由精确AST和原核规范化等价，取得一条实际的源公理原核证明。 -/
theorem to_source {p : Source.Sentence} {q : SetTheory.Definitional.Project.Sentence}
    (hq : SetTheory.ZF q)
    (h : Translation.sentence p = Normalization.formula (SetTheory.Definitional.Project.fo_sentence q)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) := by
  rw [h]
  apply FirstOrder.Derives.iff_elim_left (Normalization.equivalent _)
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := nativeZF) (free := []) ⟨q, hq, rfl⟩)

theorem to_native {p : Source.Sentence} {q : SetTheory.Definitional.Project.Sentence}
    (hp : Source.SetLanguage.ZF p)
    (h : Translation.sentence p = Normalization.formula (SetTheory.Definitional.Project.fo_sentence q)) :
    FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence q) := by
  apply FirstOrder.Derives.iff_elim_right (Normalization.equivalent _)
  rw [← h]
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := sourceZF) (free := []) ⟨p, hp, rfl⟩)

theorem source_extensionality : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.extensionality) :=
  to_source .extensionality extensionality_ast
theorem source_emptySet : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.emptySet) :=
  to_source .emptySet emptySet_ast
theorem source_pairing : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.pairing) :=
  to_source .pairing pairing_ast
theorem source_union : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.union) :=
  to_source .union union_ast
theorem source_powerSet : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.powerSet) :=
  to_source .powerSet powerSet_ast

theorem native_extensionality : FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) :=
  to_native .extensionality extensionality_ast
theorem native_emptySet : FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.emptySet) :=
  to_native .emptySet emptySet_ast
theorem native_pairing : FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.pairing) :=
  to_native .pairing pairing_ast
theorem native_union : FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.union) :=
  to_native .union union_ast
theorem native_powerSet : FirstOrder.Derives sourceZF [] (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.powerSet) :=
  to_native .powerSet powerSet_ast
end PPAC.Migration.ZFEquivalence
