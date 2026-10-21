import PPAC.Migration.Internal.StructuralListProjectionRecursion

/-! head/tail各实例的原核闭句：全内部集合总单值算子和真实内部自然迭代。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListProjection
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax

def totalSentence (head : Bool) : Source.Sentence := ((((omega 0).imp (NaturalRecursionSyntax.relationTotal (matrix head) (params 0))) : Formula 1)).close

def functionalSentence (head : Bool) : Source.Sentence := ((((omega 0).imp (NaturalRecursionSyntax.relationFunctional (matrix head) (params 0))) : Formula 1)).close

def rangeSentence (head : Bool) : Source.Sentence := ((((omega 0).imp (NaturalEvaluationRange.range (matrix head) (params 0) 0)) : Formula 1)).close

def consSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((consCode 0 1 2 3).imp ((step head 0 3 4).imp (Formula.equal 4 (if head then 1 else 2))))))) : Formula 5)).close

def nilSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((nilCode 0 1).imp ((step head 0 1 2).imp (empty 2)))) : Formula 3)).close

def offConsSentence (head : Bool) : Source.Sentence := (((((hasCons head 0 1).neg).imp ((step head 0 1 2).imp (empty 2))) : Formula 3)).close

def recursorsSentence (head : Bool) : Source.Sentence := ((((omega 0).imp (recursors head 0 1)) : Formula 2)).close

def fiberSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (iterationFiber head 0 1 2))) : Formula 3)).close

def closureSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((iteration head 0 1 2 3).imp (Formula.mem 3 0)))) : Formula 4)).close

def zeroSentence (head : Bool) : Source.Sentence := ((((empty 2).imp ((iteration head 0 1 2 3).imp (Formula.equal 3 1))) : Formula 4)).close

def nextSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp ((successor 3 2).imp ((iteration head 0 1 2 4).imp ((iteration head 0 1 3 5).imp (step head 0 4 5)))))) : Formula 6)).close

theorem source_total (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (totalSentence head) := by
  apply close_derives
  apply Derives.impI

  exact StructuralListProjectionRecursion.total head (params (0 : Fin 1)) (.hyp (Or.inl rfl))

theorem total_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (totalSentence head)) := TheoryTransport.sentence (source_total head)

theorem native_total (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (totalSentence head)) := ZFReplay.replay (total_kernel_certificate head)

theorem source_functional (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (functionalSentence head) := by
  apply close_derives
  apply Derives.impI

  let Δ : Context 1 := Context.add (omega 0) (Source.SetLanguage.ZF.at 1)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 1

  exact StructuralListProjectionRecursion.functional hZ head (params (0 : Fin 1)) (.hyp (Or.inl rfl))

theorem functional_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (functionalSentence head)) := TheoryTransport.sentence (source_functional head)

theorem native_functional (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (functionalSentence head)) := ZFReplay.replay (functional_kernel_certificate head)

theorem source_range (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (rangeSentence head) := by
  apply close_derives
  apply Derives.impI

  let Δ : Context 1 := Context.add (omega 0) (Source.SetLanguage.ZF.at 1)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 1

  exact StructuralListProjectionRecursion.range hZ head (params (0 : Fin 1)) (.hyp (Or.inl rfl))

theorem range_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rangeSentence head)) := TheoryTransport.sentence (source_range head)

theorem native_range (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rangeSentence head)) := ZFReplay.replay (range_kernel_certificate head)

theorem source_cons (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (consSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 5 := Context.add (step head 0 3 4) (Context.add (consCode 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5

  exact StructuralListProjection.on_cons hZ head 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem cons_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consSentence head)) := TheoryTransport.sentence (source_cons head)

theorem native_cons (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consSentence head)) := ZFReplay.replay (cons_kernel_certificate head)

theorem source_nil (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (nilSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (step head 0 1 2) (Context.add (nilCode 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListProjection.on_nil hZ head 0 1 2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nil_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nilSentence head)) := TheoryTransport.sentence (source_nil head)

theorem native_nil (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nilSentence head)) := ZFReplay.replay (nil_kernel_certificate head)

theorem source_offCons (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (offConsSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  exact StructuralListProjection.off_cons head 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem offCons_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (offConsSentence head)) := TheoryTransport.sentence (source_offCons head)

theorem native_offCons (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (offConsSentence head)) := ZFReplay.replay (offCons_kernel_certificate head)

theorem source_recursors (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (recursorsSentence head) := by
  apply close_derives
  apply Derives.impI

  let Δ : Context 2 := Context.add (omega 0) (Source.SetLanguage.ZF.at 2)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 2

  exact StructuralListProjectionRecursion.actual_recursors hZ head 0 1 (.hyp (Or.inl rfl))

theorem recursors_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursorsSentence head)) := TheoryTransport.sentence (source_recursors head)

theorem native_recursors (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursorsSentence head)) := ZFReplay.replay (recursors_kernel_certificate head)

theorem source_fiber (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (fiberSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListProjectionRecursion.actual_fiber hZ head 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberSentence head)) := TheoryTransport.sentence (source_fiber head)

theorem native_fiber (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberSentence head)) := ZFReplay.replay (fiber_kernel_certificate head)

theorem source_closure (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (closureSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (iteration head 0 1 2 3) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListProjectionRecursion.iteration_range hZ head 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem closure_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closureSentence head)) := TheoryTransport.sentence (source_closure head)

theorem native_closure (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closureSentence head)) := ZFReplay.replay (closure_kernel_certificate head)

theorem source_zero (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (zeroSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  exact StructuralListProjectionRecursion.iteration_zero head 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem zero_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroSentence head)) := TheoryTransport.sentence (source_zero head)

theorem native_zero (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroSentence head)) := ZFReplay.replay (zero_kernel_certificate head)

theorem source_next (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (nextSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (iteration head 0 1 3 5) (Context.add (iteration head 0 1 2 4) (Context.add (successor 3 2) (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListProjectionRecursion.iteration_step hZ head 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem next_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nextSentence head)) := TheoryTransport.sentence (source_next head)

theorem native_next (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nextSentence head)) := ZFReplay.replay (next_kernel_certificate head)

end PPAC.Migration.Internal.ObjectStructuralListProjection
