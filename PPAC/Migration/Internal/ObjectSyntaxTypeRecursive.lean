import PPAC.Migration.Internal.SyntaxTypeSystem

/-! 历史无关全11类型递归式与实际内部类型系统存在的原nativeZF闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxTypeRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PowerSetSyntax SyntaxTypeRecursionSyntax SyntaxTypeStateSyntax SyntaxTypeEvaluationSyntax SyntaxTypeJudgmentSyntax SyntaxTypeRecursiveSyntax SyntaxTypeSystemSyntax

def readSentence {m} (w c h n x b f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem x n).imp ((graph w c h n).imp ((SyntaxContextReadSyntax.read h x b f).iff (typed w c x b f)))))).close

theorem source_read {m} (w c h n x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readSentence w c h n x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem x n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeReadTransfer.plain hZ w c h n x b f h0 h1 h2 h3

theorem read_kernel_certificate {m} (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readSentence w c h n x b f)) := TheoryTransport.sentence (source_read w c h n x b f)

theorem native_read {m} (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readSentence w c h n x b f)) := ZFReplay.replay (read_kernel_certificate w c h n x b f)

def advancedSentence {m} (w c h n x b f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem x n).imp ((graph w c h n).imp ((SyntaxContextReadSyntax.advanced h x b f).iff (advancedTyped w c x b f)))))).close

theorem source_advanced {m} (w c h n x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedSentence w c h n x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem x n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeReadTransfer.advanced hZ w c h n x b f h0 h1 h2 h3

theorem advanced_kernel_certificate {m} (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedSentence w c h n x b f)) := TheoryTransport.sentence (source_advanced w c h n x b f)

theorem native_advanced {m} (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedSentence w c h n x b f)) := ZFReplay.replay (advanced_kernel_certificate w c h n x b f)

def checkSentence {m} (advance : Bool) (w c h n x b f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem x n).imp ((graph w c h n).imp ((SyntaxContextReadSyntax.check advance h x b f).iff (stepCheck advance w c x b f)))))).close

theorem source_check {m} (advance : Bool) (w c h n x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkSentence advance w c h n x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem x n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeReadTransfer.check_iff hZ advance w c h n x b f h0 h1 h2 h3

theorem check_kernel_certificate {m} (advance : Bool) (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkSentence advance w c h n x b f)) := TheoryTransport.sentence (source_check advance w c h n x b f)

theorem native_check {m} (advance : Bool) (w c h n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkSentence advance w c h n x b f)) := ZFReplay.replay (check_kernel_certificate advance w c h n x b f)

def singleSentence {m} (tag : Nat) (advance : Bool) (w c b f h n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((graph w c h n).imp ((SyntaxLogicalSyntax.single tag advance w b f h n).iff (singleCase tag advance w c b f n))))).close

theorem source_single {m} (tag : Nat) (advance : Bool) (w c b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleSentence tag advance w c b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeCaseTransfer.single_iff hZ tag advance w c b f h n h0 h1 h2

theorem single_kernel_certificate {m} (tag : Nat) (advance : Bool) (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleSentence tag advance w c b f h n)) := TheoryTransport.sentence (source_single tag advance w c b f h n)

theorem native_single {m} (tag : Nat) (advance : Bool) (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleSentence tag advance w c b f h n)) := ZFReplay.replay (single_kernel_certificate tag advance w c b f h n)

def binarySentence {m} (kind : Fin 4) (w c b f h n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((graph w c h n).imp ((SyntaxLogicalSyntax.binary kind w b f h n).iff (binaryCase kind w c b f n))))).close

theorem source_binary {m} (kind : Fin 4) (w c b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binarySentence kind w c b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeCaseTransfer.binary_iff hZ kind w c b f h n h0 h1 h2

theorem binary_kernel_certificate {m} (kind : Fin 4) (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binarySentence kind w c b f h n)) := TheoryTransport.sentence (source_binary kind w c b f h n)

theorem native_binary {m} (kind : Fin 4) (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binarySentence kind w c b f h n)) := ZFReplay.replay (binary_kernel_certificate kind w c b f h n)

def localSentence {m} (w c b f h n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((graph w c h n).imp ((SyntaxFormulaLocalSyntax.localType w b f h n).iff (allCases w c n b f))))).close

theorem source_local {m} (w c b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (localSentence w c b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (graph w c h n) := .hyp (Or.inl rfl)
  exact SyntaxTypeLocalTransfer.all_iff hZ w c b f h n h0 h1 h2

theorem local_kernel_certificate {m} (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (localSentence w c b f h n)) := TheoryTransport.sentence (source_local w c b f h n)

theorem native_local {m} (w c b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (localSentence w c b f h n)) := ZFReplay.replay (local_kernel_certificate w c b f h n)

def atStateSentence {m} (w a c b f h n v : Fin m) : Source.Sentence := ((omega w).imp ((powerOf a w).imp ((powerOf c a).imp ((Formula.mem n w).imp ((graph w c h n).imp ((state w c n h v).imp ((edge v b f).iff (criterion w c n b f)))))))).close

theorem source_atState {m} (w a c b f h n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atStateSentence w a c b f h n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h v) (Context.add (graph w c h n) (Context.add (Formula.mem n w) (Context.add (powerOf c a) (Context.add (powerOf a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (powerOf c a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (graph w c h n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (state w c n h v) := .hyp (Or.inl rfl)
  exact SyntaxTypeRecursive.at_state hZ w a c b f h n v h0 h1 h2 h3 h4 h5

theorem atState_kernel_certificate {m} (w a c b f h n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atStateSentence w a c b f h n v)) := TheoryTransport.sentence (source_atState w a c b f h n v)

theorem native_atState {m} (w a c b f h n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atStateSentence w a c b f h n v)) := ZFReplay.replay (atState_kernel_certificate w a c b f h n v)

def atValueSentence {m} (w a c n v b f : Fin m) : Source.Sentence := ((omega w).imp ((powerOf a w).imp ((powerOf c a).imp ((Formula.mem n w).imp ((evaluation w c n v).imp ((typed w c n b f).iff (criterion w c n b f))))))).close

theorem source_atValue {m} (w a c n v b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atValueSentence w a c n v b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add (Formula.mem n w) (Context.add (powerOf c a) (Context.add (powerOf a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (powerOf c a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeRecursive.at_value hZ w a c n v b f h0 h1 h2 h3 h4

theorem atValue_kernel_certificate {m} (w a c n v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atValueSentence w a c n v b f)) := TheoryTransport.sentence (source_atValue w a c n v b f)

theorem native_atValue {m} (w a c n v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atValueSentence w a c n v b f)) := ZFReplay.replay (atValue_kernel_certificate w a c n v b f)

def recursiveSentence {m} (w a c n b f : Fin m) : Source.Sentence := ((omega w).imp ((powerOf a w).imp ((powerOf c a).imp ((typed w c n b f).iff (criterion w c n b f))))).close

theorem source_recursive {m} (w a c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveSentence w a c n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (powerOf c a) (Context.add (powerOf a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (powerOf c a) := .hyp (Or.inl rfl)
  exact SyntaxTypeRecursive.recursive_iff hZ w a c n b f h0 h1 h2

theorem recursive_kernel_certificate {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveSentence w a c n b f)) := TheoryTransport.sentence (source_recursive w a c n b f)

theorem native_recursive {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveSentence w a c n b f)) := ZFReplay.replay (recursive_kernel_certificate w a c n b f)

def universalSentence {m} (w a c : Fin m) : Source.Sentence := ((omega w).imp ((powerOf a w).imp ((powerOf c a).imp (universalLaw w c)))).close

theorem source_universal {m} (w a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (universalSentence w a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (powerOf c a) (Context.add (powerOf a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (powerOf c a) := .hyp (Or.inl rfl)
  exact SyntaxTypeSystem.all_law hZ w a c h0 h1 h2

theorem universal_kernel_certificate {m} (w a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (universalSentence w a c)) := TheoryTransport.sentence (source_universal w a c)

theorem native_universal {m} (w a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (universalSentence w a c)) := ZFReplay.replay (universal_kernel_certificate w a c)

def actualSystemSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp (system w)).close

theorem source_actualSystem {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualSystemSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTypeSystem.actual_system hZ w h0

theorem actualSystem_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualSystemSentence w)) := TheoryTransport.sentence (source_actualSystem w)

theorem native_actualSystem {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualSystemSentence w)) := ZFReplay.replay (actualSystem_kernel_certificate w)

def existenceSentence : Source.Sentence := existsSystem

theorem source_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := by
  have hh := SyntaxTypeSystem.existence (ZFContext.source_ZF 0)
  have hId : (Fin.elim0 : Fin 0 → Fin 0) = id := by funext i; exact Fin.elim0 i
  simpa only [existenceSentence, hId, Reverse.source_rename_id] using hh

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existenceSentence) := ZFReplay.replay existence_kernel_certificate
end PPAC.Migration.Internal.ObjectSyntaxTypeRecursive
