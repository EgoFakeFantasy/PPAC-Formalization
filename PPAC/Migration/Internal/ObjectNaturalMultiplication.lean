import PPAC.Migration.Internal.NaturalMultiplicationZero

/-! 乘法的自然数存在唯一、闭包、两侧零点和后继递推均有原ZF核闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectNaturalMultiplication
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax NaturalMultiplicationSyntax

def fiberSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp (NaturalMultiplicationSyntax.fiber 0 1 2)))).close

def closureSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp
  ((product 0 1 2 3).imp (.mem 3 0)))).close

def zeroSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp
  ((empty 2).imp ((product 0 1 2 3).iff (empty 3))))).close

def successorSentence : Source.Sentence := ((omega (0 : Fin 6)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp
  ((successor 3 2).imp ((product 0 1 2 4).imp ((product 0 1 3 5).iff (NaturalAdditionSyntax.sum 0 4 1 5))))))).close

def leftZeroSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((empty 1).imp (.all
  ((Formula.mem (Fin.last 2) (0 : Fin 2).castSucc).imp (product (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2) (1 : Fin 2).castSucc))))).close

theorem add_certificate_at (m : Nat) : Derives (Source.SetLanguage.ZF.at m)
    ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) :=
  ObjectNaturalAddition.recursor_certificate_at m

theorem mul_certificate_at (m : Nat) : Derives (Source.SetLanguage.ZF.at m)
    ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) :=
  ObjectTransitiveCover.closed_at (NaturalRecursion.source_uniqueness NaturalMultiplicationStep.matrix) m

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationCore.exists_unique (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.source_ZF 3) _) _) _)
    0 1 2 (add (add (add (add_certificate_at 3) _) _) _) (add (add (add (mul_certificate_at 3) _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_closure : Derives (Source.SetLanguage.ZF.at 0) closureSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (Source.SetLanguage.ZF.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  exact NaturalMultiplicationCore.closure 0 1 2 3 (add (add (add he _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inl rfl))

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationLaws.zero_iff (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.source_ZF 4) _) _) _)
    0 1 2 3 (add (add (add (add_certificate_at 4) _) _) _) (add (add (add (mul_certificate_at 4) _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationLaws.successor_iff (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add
    (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.source_ZF 6) _) _) _) _) _)
    0 1 2 3 4 5 (add (add (add (add (add (add_certificate_at 6) _) _) _) _) _) (add (add (add (add (add (mul_certificate_at 6) _) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_leftZero : Derives (Source.SetLanguage.ZF.at 0) leftZeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hs : Derives (Source.SetLanguage.ZF.at 2) ((Source.SetLanguage.separation NaturalMultiplicationZero.matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation NaturalMultiplicationZero.matrix, rfl⟩
  exact NaturalMultiplicationZero.all_left_zero (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.source_ZF 2) _) _) 0 1
    (add (add (add_certificate_at 2) _) _) (add (add (mul_certificate_at 2) _) _) (add (add hs _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))


theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber
theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence fiberSentence) :=
  ZFReplay.replay fiber_kernel_certificate


theorem closure_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence closureSentence) := TheoryTransport.sentence source_closure
theorem native_closure : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence closureSentence) :=
  ZFReplay.replay closure_kernel_certificate


theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero
theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate


theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor
theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  ZFReplay.replay successor_kernel_certificate


theorem leftZero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftZeroSentence) := TheoryTransport.sentence source_leftZero
theorem native_leftZero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftZeroSentence) :=
  ZFReplay.replay leftZero_kernel_certificate
end PPAC.Migration.Internal.ObjectNaturalMultiplication
