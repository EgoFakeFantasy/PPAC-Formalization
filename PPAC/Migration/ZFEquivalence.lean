import PPAC.Migration.FormulaEquivalence
import PPAC.Migration.Contract
import PPAC.Migration.Presentation
import PPAC.Migration.SourceTheory

/-! 源Replacement版ZF与原Collection版ZF的对应：本模块完成七条固定公理。
分离模式的源矩阵对应见SeparationSyntax；全Collection/Replacement对应仍待证明。 -/
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
open FormulaEquivalence

def infinityPresentation (native : Bool) : Source.Sentence :=
  .ex ((Source.Formula.ex (if native then (Source.SetLanguage.empty 1).conj (Source.Formula.mem 1 0)
    else (Source.Formula.mem 1 0).conj (Source.SetLanguage.empty 1))).conj
    (Source.Formula.all ((Source.Formula.mem 1 0).imp (Source.Formula.ex (if native then (Source.SetLanguage.successor 2 1).conj (Source.Formula.mem 2 0)
      else (Source.Formula.mem 2 0).conj (Source.SetLanguage.successor 2 1))))))

def foundationPresentation (native : Bool) : Source.Sentence :=
  .all ((Source.SetLanguage.nonempty 0).imp
    (Source.Formula.ex ((Source.Formula.mem 1 0).conj (Source.Formula.all (if native then (Source.Formula.mem 2 0).imp (Source.Formula.mem 2 1).neg
      else (Source.Formula.mem 2 1).imp (Source.Formula.mem 2 0).neg)))))

theorem source_infinity_ast : Source.SetLanguage.infinity = infinityPresentation false := by decide +kernel
theorem native_infinity_ast : Reverse.sentence
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity) = infinityPresentation true := by decide +kernel

theorem source_foundation_ast : Source.SetLanguage.foundation = foundationPresentation false := by decide +kernel
theorem native_foundation_ast : Reverse.sentence
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation) = foundationPresentation true := by decide +kernel

theorem infinity_logical : Equivalent (infinityPresentation false) (infinityPresentation true) :=
  Equivalent.ex (Equivalent.conj (Equivalent.ex (conj_comm _ _))
    (Equivalent.all (Equivalent.imp (Equivalent.refl _) (Equivalent.ex (conj_comm _ _)))))

theorem foundation_logical : Equivalent (foundationPresentation false) (foundationPresentation true) :=
  Equivalent.all (Equivalent.imp (Equivalent.refl _)
    (Equivalent.ex (Equivalent.conj (Equivalent.refl _) (Equivalent.all (curry_swap _ _ .bot)))))

/-- 无穷与基础的差异是内部逻辑重排，不引入对象选择或语义完备性。 -/
theorem logical_bridge {p : Source.Sentence} {q : SetTheory.Definitional.Project.Sentence}
    (h : Equivalent p (Reverse.sentence (SetTheory.Definitional.Project.fo_sentence q)))
    {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Translation.sentence p) (SetTheory.Definitional.Project.fo_sentence q)) :=
  Normalization.iff_trans h.closed
    (Normalization.iff_symm (Reverse.sentence_equivalent _))

theorem infinity_bridge {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Translation.sentence Source.SetLanguage.infinity)
      (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity)) := by
  apply logical_bridge
  rw [source_infinity_ast, native_infinity_ast]
  exact infinity_logical

theorem foundation_bridge {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Translation.sentence Source.SetLanguage.foundation)
      (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation)) := by
  apply logical_bridge
  rw [source_foundation_ast, native_foundation_ast]
  exact foundation_logical

theorem source_infinity : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.infinity) := by
  apply FirstOrder.Derives.iff_elim_right infinity_bridge
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := nativeZF) (free := [])
      ⟨SetTheory.Axioms.infinity, SetTheory.ZF.Axiom.infinity, rfl⟩)

theorem source_foundation : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.foundation) := by
  apply FirstOrder.Derives.iff_elim_right foundation_bridge
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := nativeZF) (free := [])
      ⟨SetTheory.Axioms.foundation, SetTheory.ZF.Axiom.foundation, rfl⟩)

theorem native_infinity : FirstOrder.Derives sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity) := by
  apply FirstOrder.Derives.iff_elim_left infinity_bridge
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := sourceZF) (free := [])
      ⟨Source.SetLanguage.infinity, Source.SetLanguage.IsZFAxiom.infinity, rfl⟩)

theorem native_foundation : FirstOrder.Derives sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation) := by
  apply FirstOrder.Derives.iff_elim_left foundation_bridge
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := sourceZF) (free := [])
      ⟨Source.SetLanguage.foundation, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩)
end PPAC.Migration.ZFEquivalence
