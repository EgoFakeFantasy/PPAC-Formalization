import PPAC.Migration.Internal.SyntaxLogicalReject

/-! 全内部上下文集合读取与七种逻辑局部分支的完整闭句及原nativeZF推导证书。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxLogical
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxTermSyntax SyntaxLogicalSyntax SyntaxLogicalDecode SyntaxContextReadSyntax

def readAtValueSentence {m} (h d x v b f : Fin m) : Source.Sentence := ((functionOn h d).imp ((edge h x v).imp ((read h x b f).iff (edge v b f)))).close

theorem source_readAtValue {m} (h d x v b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readAtValueSentence h d x v b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (edge h x v) (Context.add (functionOn h d) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (functionOn h d) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (edge h x v) := .hyp (Or.inl rfl)
  exact SyntaxContextRead.at_value hZ h d x v b f h0 h1

theorem readAtValue_kernel_certificate {m} (h d x v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readAtValueSentence h d x v b f)) := TheoryTransport.sentence (source_readAtValue h d x v b f)

theorem native_readAtValue {m} (h d x v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readAtValueSentence h d x v b f)) := ZFReplay.replay (readAtValue_kernel_certificate h d x v b f)

def advancedAtSuccessorSentence {m} (h x b f k : Fin m) : Source.Sentence := ((successor k b).imp ((advanced h x b f).iff (read h x k f))).close

theorem source_advancedAtSuccessor {m} (h x b f k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedAtSuccessorSentence h x b f k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (successor k b) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (successor k b) := .hyp (Or.inl rfl)
  exact SyntaxContextRead.at_successor hZ h x b f k h0

theorem advancedAtSuccessor_kernel_certificate {m} (h x b f k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedAtSuccessorSentence h x b f k)) := TheoryTransport.sentence (source_advancedAtSuccessor h x b f k)

theorem native_advancedAtSuccessor {m} (h x b f k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedAtSuccessorSentence h x b f k)) := ZFReplay.replay (advancedAtSuccessor_kernel_certificate h x b f k)

def successorContextSentence {m} (w b f k : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((successor k b).imp ((contexts w k f).conj (.mem b k))))).close

theorem source_successorContext {m} (w b f k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorContextSentence w b f k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k b) (Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor k b) := .hyp (Or.inl rfl)
  exact SyntaxContextRead.successor_context hZ w b f k h0 h1 h2

theorem successorContext_kernel_certificate {m} (w b f k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorContextSentence w b f k)) := TheoryTransport.sentence (source_successorContext w b f k)

theorem native_successorContext {m} (w b f k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorContextSentence w b f k)) := ZFReplay.replay (successorContext_kernel_certificate w b f k)

def singleTypesSentence {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp ((single tag advance w b f h n).iff (singleTypes advance w b f h x)))).close

theorem source_singleTypes {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleTypesSentence tag advance w b f h x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalTyping.single_iff hZ tag advance w b f h x n h0 h1

theorem singleTypes_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleTypesSentence tag advance w b f h x n)) := TheoryTransport.sentence (source_singleTypes tag advance w b f h x n)

theorem native_singleTypes {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleTypesSentence tag advance w b f h x n)) := ZFReplay.replay (singleTypes_kernel_certificate tag advance w b f h x n)

def negationTypesSentence {m} (w b f h x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode 4 w x n).imp ((negation w b f h n).iff ((contexts w b f).conj (read h x b f))))).close

theorem source_negationTypes {m} (w b f h x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationTypesSentence w b f h x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode 4 w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalTyping.single_iff hZ 4 false w b f h x n h0 h1

theorem negationTypes_kernel_certificate {m} (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationTypesSentence w b f h x n)) := TheoryTransport.sentence (source_negationTypes w b f h x n)

theorem native_negationTypes {m} (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationTypesSentence w b f h x n)) := ZFReplay.replay (negationTypes_kernel_certificate w b f h x n)

def binaryTypesSentence {m} (kind : Fin 4) (w b f h x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((binary kind w b f h n).iff (binaryTypes w b f h x y)))).close

theorem source_binaryTypes {m} (kind : Fin 4) (w b f h x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryTypesSentence kind w b f h x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalTyping.binary_iff hZ kind w b f h x y n h0 h1

theorem binaryTypes_kernel_certificate {m} (kind : Fin 4) (w b f h x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryTypesSentence kind w b f h x y n)) := TheoryTransport.sentence (source_binaryTypes kind w b f h x y n)

theorem native_binaryTypes {m} (kind : Fin 4) (w b f h x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryTypesSentence kind w b f h x y n)) := ZFReplay.replay (binaryTypes_kernel_certificate kind w b f h x y n)

def quantifierTypesSentence {m} (universal : Bool) (w b f h x n k : Fin m) : Source.Sentence := ((omega w).imp ((singleCode (quantifierTag universal) w x n).imp ((successor k b).imp ((quantified universal w b f h n).iff ((contexts w b f).conj (read h x k f)))))).close

theorem source_quantifierTypes {m} (universal : Bool) (w b f h x n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierTypesSentence universal w b f h x n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k b) (Context.add (singleCode (quantifierTag universal) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode (quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor k b) := .hyp (Or.inl rfl)
  exact SyntaxLogicalTyping.quantified_iff hZ universal w b f h x n k h0 h1 h2

theorem quantifierTypes_kernel_certificate {m} (universal : Bool) (w b f h x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierTypesSentence universal w b f h x n k)) := TheoryTransport.sentence (source_quantifierTypes universal w b f h x n k)

theorem native_quantifierTypes {m} (universal : Bool) (w b f h x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierTypesSentence universal w b f h x n k)) := ZFReplay.replay (quantifierTypes_kernel_certificate universal w b f h x n k)

def singleExistsSentence {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((Formula.mem x w).imp ((check advance h x b f).imp (existsSingle tag advance w b f h x))))).close

theorem source_singleExists {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleExistsSentence tag advance w b f h x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (check advance h x b f) (Context.add (Formula.mem x w) (Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (check advance h x b f) := .hyp (Or.inl rfl)
  exact SyntaxLogicalExistence.single_exists hZ tag advance w b f h x h0 h1 h2 h3

theorem singleExists_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleExistsSentence tag advance w b f h x)) := TheoryTransport.sentence (source_singleExists tag advance w b f h x)

theorem native_singleExists {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleExistsSentence tag advance w b f h x)) := ZFReplay.replay (singleExists_kernel_certificate tag advance w b f h x)

def binaryExistsSentence {m} (kind : Fin 4) (w b f h x y : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((Formula.mem x w).imp ((Formula.mem y w).imp (((read h x b f).conj (read h y b f)).imp (existsBinary kind w b f h x y)))))).close

theorem source_binaryExists {m} (kind : Fin 4) (w b f h x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryExistsSentence kind w b f h x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((read h x b f).conj (read h y b f)) (Context.add (Formula.mem y w) (Context.add (Formula.mem x w) (Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem y w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((read h x b f).conj (read h y b f)) := .hyp (Or.inl rfl)
  exact SyntaxLogicalExistence.binary_exists hZ kind w b f h x y h0 h1 h2 h3 h4

theorem binaryExists_kernel_certificate {m} (kind : Fin 4) (w b f h x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryExistsSentence kind w b f h x y)) := TheoryTransport.sentence (source_binaryExists kind w b f h x y)

theorem native_binaryExists {m} (kind : Fin 4) (w b f h x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryExistsSentence kind w b f h x y)) := ZFReplay.replay (binaryExists_kernel_certificate kind w b f h x y)

def quantifierExistsSentence {m} (universal : Bool) (w b f h x k : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp ((Formula.mem x w).imp ((successor k b).imp ((read h x k f).imp (existsSingle (quantifierTag universal) true w b f h x)))))).close

theorem source_quantifierExists {m} (universal : Bool) (w b f h x k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierExistsSentence universal w b f h x k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (read h x k f) (Context.add (successor k b) (Context.add (Formula.mem x w) (Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor k b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (read h x k f) := .hyp (Or.inl rfl)
  exact SyntaxLogicalExistence.quantified_exists hZ universal w b f h x k h0 h1 h2 h3 h4

theorem quantifierExists_kernel_certificate {m} (universal : Bool) (w b f h x k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierExistsSentence universal w b f h x k)) := TheoryTransport.sentence (source_quantifierExists universal w b f h x k)

theorem native_quantifierExists {m} (universal : Bool) (w b f h x k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierExistsSentence universal w b f h x k)) := ZFReplay.replay (quantifierExists_kernel_certificate universal w b f h x k)

def singleFieldsSentence {m} (tag : Nat) (w x y n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp ((singleCode tag w y n).imp (Formula.equal x y)))).close

theorem source_singleFields {m} (tag : Nat) (w x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleFieldsSentence tag w x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode tag w y n) (Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (singleCode tag w y n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.single_fields hZ tag w x y n h0 h1 h2

theorem singleFields_kernel_certificate {m} (tag : Nat) (w x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleFieldsSentence tag w x y n)) := TheoryTransport.sentence (source_singleFields tag w x y n)

theorem native_singleFields {m} (tag : Nat) (w x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleFieldsSentence tag w x y n)) := ZFReplay.replay (singleFields_kernel_certificate tag w x y n)

def binaryFieldsSentence {m} (kind : Fin 4) (w x y u v n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((binaryCode kind w u v n).imp ((Formula.equal x u).conj (.equal y v))))).close

theorem source_binaryFields {m} (kind : Fin 4) (w x y u v n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryFieldsSentence kind w x y u v n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode kind w u v n) (Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (binaryCode kind w u v n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.binary_fields hZ kind w x y u v n h0 h1 h2

theorem binaryFields_kernel_certificate {m} (kind : Fin 4) (w x y u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryFieldsSentence kind w x y u v n)) := TheoryTransport.sentence (source_binaryFields kind w x y u v n)

theorem native_binaryFields {m} (kind : Fin 4) (w x y u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryFieldsSentence kind w x y u v n)) := ZFReplay.replay (binaryFields_kernel_certificate kind w x y u v n)

def singleBoundSentence {m} (tag : Nat) (w x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp (Formula.mem x n))).close

theorem source_singleBound {m} (tag : Nat) (w x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleBoundSentence tag w x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.single_bound hZ tag w x n h0 h1

theorem singleBound_kernel_certificate {m} (tag : Nat) (w x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleBoundSentence tag w x n)) := TheoryTransport.sentence (source_singleBound tag w x n)

theorem native_singleBound {m} (tag : Nat) (w x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleBoundSentence tag w x n)) := ZFReplay.replay (singleBound_kernel_certificate tag w x n)

def binaryBoundsSentence {m} (kind : Fin 4) (w x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((Formula.mem x n).conj (.mem y n)))).close

theorem source_binaryBounds {m} (kind : Fin 4) (w x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryBoundsSentence kind w x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.binary_bounds hZ kind w x y n h0 h1

theorem binaryBounds_kernel_certificate {m} (kind : Fin 4) (w x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryBoundsSentence kind w x y n)) := TheoryTransport.sentence (source_binaryBounds kind w x y n)

theorem native_binaryBounds {m} (kind : Fin 4) (w x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryBoundsSentence kind w x y n)) := ZFReplay.replay (binaryBounds_kernel_certificate kind w x y n)

def singleUniqueSentence {m} (tag : Nat) (w x n r : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp ((singleCode tag w x r).imp (Formula.equal n r)))).close

theorem source_singleUnique {m} (tag : Nat) (w x n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleUniqueSentence tag w x n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode tag w x r) (Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (singleCode tag w x r) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.single_unique hZ tag w x n r h0 h1 h2

theorem singleUnique_kernel_certificate {m} (tag : Nat) (w x n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleUniqueSentence tag w x n r)) := TheoryTransport.sentence (source_singleUnique tag w x n r)

theorem native_singleUnique {m} (tag : Nat) (w x n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleUniqueSentence tag w x n r)) := ZFReplay.replay (singleUnique_kernel_certificate tag w x n r)

def binaryUniqueSentence {m} (kind : Fin 4) (w x y n r : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((binaryCode kind w x y r).imp (Formula.equal n r)))).close

theorem source_binaryUnique {m} (kind : Fin 4) (w x y n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryUniqueSentence kind w x y n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode kind w x y r) (Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (binaryCode kind w x y r) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.binary_unique hZ kind w x y n r h0 h1 h2

theorem binaryUnique_kernel_certificate {m} (kind : Fin 4) (w x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryUniqueSentence kind w x y n r)) := TheoryTransport.sentence (source_binaryUnique kind w x y n r)

theorem native_binaryUnique {m} (kind : Fin 4) (w x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryUniqueSentence kind w x y n r)) := ZFReplay.replay (binaryUnique_kernel_certificate kind w x y n r)

def singleRangeSentence {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Source.Sentence := ((omega w).imp ((single tag advance w b f h n).imp (Formula.mem n w))).close

theorem source_singleRange {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleRangeSentence tag advance w b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (single tag advance w b f h n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (single tag advance w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.single_range hZ tag advance w b f h n h0 h1

theorem singleRange_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleRangeSentence tag advance w b f h n)) := TheoryTransport.sentence (source_singleRange tag advance w b f h n)

theorem native_singleRange {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleRangeSentence tag advance w b f h n)) := ZFReplay.replay (singleRange_kernel_certificate tag advance w b f h n)

def singleDecodeSentence {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Source.Sentence := ((omega w).imp ((single tag advance w b f h n).iff (singleDecoded tag advance w b f h n))).close

theorem source_singleDecode {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleDecodeSentence tag advance w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxLogicalDecode.single_decode_iff hZ tag advance w b f h n h0

theorem singleDecode_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleDecodeSentence tag advance w b f h n)) := TheoryTransport.sentence (source_singleDecode tag advance w b f h n)

theorem native_singleDecode {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleDecodeSentence tag advance w b f h n)) := ZFReplay.replay (singleDecode_kernel_certificate tag advance w b f h n)

def binaryRangeSentence {m} (kind : Fin 4) (w b f h n : Fin m) : Source.Sentence := ((omega w).imp ((binary kind w b f h n).imp (Formula.mem n w))).close

theorem source_binaryRange {m} (kind : Fin 4) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryRangeSentence kind w b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binary kind w b f h n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binary kind w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalFields.binary_range hZ kind w b f h n h0 h1

theorem binaryRange_kernel_certificate {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryRangeSentence kind w b f h n)) := TheoryTransport.sentence (source_binaryRange kind w b f h n)

theorem native_binaryRange {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryRangeSentence kind w b f h n)) := ZFReplay.replay (binaryRange_kernel_certificate kind w b f h n)

def binaryDecodeSentence {m} (kind : Fin 4) (w b f h n : Fin m) : Source.Sentence := ((omega w).imp ((binary kind w b f h n).iff (binaryDecoded kind w b f h n))).close

theorem source_binaryDecode {m} (kind : Fin 4) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryDecodeSentence kind w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxLogicalDecode.binary_decode_iff hZ kind w b f h n h0

theorem binaryDecode_kernel_certificate {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryDecodeSentence kind w b f h n)) := TheoryTransport.sentence (source_binaryDecode kind w b f h n)

theorem native_binaryDecode {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryDecodeSentence kind w b f h n)) := ZFReplay.replay (binaryDecode_kernel_certificate kind w b f h n)

def singleFiberSentence {m} (tag : Nat) (w n x : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp (singleUnique tag w n x))).close

theorem source_singleFiber {m} (tag : Nat) (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleFiberSentence tag w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalDecode.single_unique hZ tag w n x h0 h1

theorem singleFiber_kernel_certificate {m} (tag : Nat) (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleFiberSentence tag w n x)) := TheoryTransport.sentence (source_singleFiber tag w n x)

theorem native_singleFiber {m} (tag : Nat) (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleFiberSentence tag w n x)) := ZFReplay.replay (singleFiber_kernel_certificate tag w n x)

def binaryFiberSentence {m} (kind : Fin 4) (w n x y : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp (binaryUnique kind w n x y))).close

theorem source_binaryFiber {m} (kind : Fin 4) (w n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryFiberSentence kind w n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalDecode.binary_unique hZ kind w n x y h0 h1

theorem binaryFiber_kernel_certificate {m} (kind : Fin 4) (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryFiberSentence kind w n x y)) := TheoryTransport.sentence (source_binaryFiber kind w n x y)

theorem native_binaryFiber {m} (kind : Fin 4) (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryFiberSentence kind w n x y)) := ZFReplay.replay (binaryFiber_kernel_certificate kind w n x y)

def singleNotCheckSentence {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode tag w x n).imp (((check advance h x b f).neg).imp ((single tag advance w b f h n).neg)))).close

theorem source_singleNotCheck {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleNotCheckSentence tag advance w b f h x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((check advance h x b f).neg) (Context.add (singleCode tag w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode tag w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((check advance h x b f).neg) := .hyp (Or.inl rfl)
  exact SyntaxLogicalReject.single_not_check hZ tag advance w b f h x n h0 h1 h2

theorem singleNotCheck_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleNotCheckSentence tag advance w b f h x n)) := TheoryTransport.sentence (source_singleNotCheck tag advance w b f h x n)

theorem native_singleNotCheck {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleNotCheckSentence tag advance w b f h x n)) := ZFReplay.replay (singleNotCheck_kernel_certificate tag advance w b f h x n)

def binaryNotReadsSentence {m} (kind : Fin 4) (w b f h x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((((read h x b f).conj (read h y b f)).neg).imp ((binary kind w b f h n).neg)))).close

theorem source_binaryNotReads {m} (kind : Fin 4) (w b f h x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryNotReadsSentence kind w b f h x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (((read h x b f).conj (read h y b f)).neg) (Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (((read h x b f).conj (read h y b f)).neg) := .hyp (Or.inl rfl)
  exact SyntaxLogicalReject.binary_not_reads hZ kind w b f h x y n h0 h1 h2

theorem binaryNotReads_kernel_certificate {m} (kind : Fin 4) (w b f h x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryNotReadsSentence kind w b f h x y n)) := TheoryTransport.sentence (source_binaryNotReads kind w b f h x y n)

theorem native_binaryNotReads {m} (kind : Fin 4) (w b f h x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryNotReadsSentence kind w b f h x y n)) := ZFReplay.replay (binaryNotReads_kernel_certificate kind w b f h x y n)

def quantifierNotReadSentence {m} (universal : Bool) (w b f h x n k : Fin m) : Source.Sentence := ((omega w).imp ((singleCode (quantifierTag universal) w x n).imp ((successor k b).imp (((read h x k f).neg).imp ((quantified universal w b f h n).neg))))).close

theorem source_quantifierNotRead {m} (universal : Bool) (w b f h x n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierNotReadSentence universal w b f h x n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((read h x k f).neg) (Context.add (successor k b) (Context.add (singleCode (quantifierTag universal) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (singleCode (quantifierTag universal) w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor k b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((read h x k f).neg) := .hyp (Or.inl rfl)
  exact SyntaxLogicalReject.quantified_not_read hZ universal w b f h x n k h0 h1 h2 h3

theorem quantifierNotRead_kernel_certificate {m} (universal : Bool) (w b f h x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierNotReadSentence universal w b f h x n k)) := TheoryTransport.sentence (source_quantifierNotRead universal w b f h x n k)

theorem native_quantifierNotRead {m} (universal : Bool) (w b f h x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierNotReadSentence universal w b f h x n k)) := ZFReplay.replay (quantifierNotRead_kernel_certificate universal w b f h x n k)

def singleUnknownTagSentence {m} (tag : Nat) (advance : Bool) (w b f h t p n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem t w).imp ((Formula.mem p w).imp (((SyntaxNumeralSyntax.numeral tag t).neg).imp ((single tag advance w b f h n).imp ((StructuralNodeSyntax.raw w t p n).imp (Formula.bot))))))).close

theorem source_singleUnknownTag {m} (tag : Nat) (advance : Bool) (w b f h t p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleUnknownTagSentence tag advance w b f h t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add (single tag advance w b f h n) (Context.add ((SyntaxNumeralSyntax.numeral tag t).neg) (Context.add (Formula.mem p w) (Context.add (Formula.mem t w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ ((SyntaxNumeralSyntax.numeral tag t).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (single tag advance w b f h n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralNodeSyntax.raw w t p n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalReject.single_unknown_tag hZ tag advance w b f h t p n h0 h1 h2 h3 h4 h5

theorem singleUnknownTag_kernel_certificate {m} (tag : Nat) (advance : Bool) (w b f h t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleUnknownTagSentence tag advance w b f h t p n)) := TheoryTransport.sentence (source_singleUnknownTag tag advance w b f h t p n)

theorem native_singleUnknownTag {m} (tag : Nat) (advance : Bool) (w b f h t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleUnknownTagSentence tag advance w b f h t p n)) := ZFReplay.replay (singleUnknownTag_kernel_certificate tag advance w b f h t p n)

def binaryUnknownTagSentence {m} (kind : Fin 4) (w b f h t p n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem t w).imp ((Formula.mem p w).imp (((SyntaxNumeralSyntax.numeral (binaryTag kind) t).neg).imp ((binary kind w b f h n).imp ((StructuralNodeSyntax.raw w t p n).imp (Formula.bot))))))).close

theorem source_binaryUnknownTag {m} (kind : Fin 4) (w b f h t p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryUnknownTagSentence kind w b f h t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add (binary kind w b f h n) (Context.add ((SyntaxNumeralSyntax.numeral (binaryTag kind) t).neg) (Context.add (Formula.mem p w) (Context.add (Formula.mem t w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ ((SyntaxNumeralSyntax.numeral (binaryTag kind) t).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (binary kind w b f h n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralNodeSyntax.raw w t p n) := .hyp (Or.inl rfl)
  exact SyntaxLogicalReject.binary_unknown_tag hZ kind w b f h t p n h0 h1 h2 h3 h4 h5

theorem binaryUnknownTag_kernel_certificate {m} (kind : Fin 4) (w b f h t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryUnknownTagSentence kind w b f h t p n)) := TheoryTransport.sentence (source_binaryUnknownTag kind w b f h t p n)

theorem native_binaryUnknownTag {m} (kind : Fin 4) (w b f h t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryUnknownTagSentence kind w b f h t p n)) := ZFReplay.replay (binaryUnknownTag_kernel_certificate kind w b f h t p n)
end PPAC.Migration.Internal.ObjectSyntaxLogical
