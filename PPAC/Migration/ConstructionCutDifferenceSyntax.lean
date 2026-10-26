/- Original-kernel pure sentence for arbitrary internal cut subtraction. -/
import PPAC.Migration.ConstructionCutDifference

namespace PPAC.Migration.ConstructionCutDifferenceSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCutDifference
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def differenceSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 4)))
      (.imp (ConstructionFractionOrder.carrier (0 : Fin 4) 1)
        (.imp (ConstructionRealCuts.cut (0 : Fin 4) 1 2)
          (.imp (ConstructionRealCuts.cut (0 : Fin 4) 1 3)
            (.imp (Project.Formula.subset (.bound (2 : Fin 4)) (.bound (3 : Fin 4)))
              (.existsE (.conj (ConstructionRealCuts.cut (1 : Fin 5) 2 0)
                (.conj (value (1 : Fin 5) 2 3 4 0)
                  (.conj (ConstructionCutAddition.sumCut (1 : Fin 5) 2 3 0 4)
                    (.conj (.forallE (.imp (ConstructionRealCuts.cut (2 : Fin 6) 3 0)
                      (.imp (ConstructionCutAddition.sumCut (2 : Fin 6) 3 4 0 5)
                        (Project.Formula.extensionalEq (.bound (0 : Fin 6)) (.bound (1 : Fin 6))))))
                      (.imp (.neg (Project.Formula.subset (.bound (4 : Fin 5)) (.bound (3 : Fin 5))))
                        (.existsE (.mem (.bound (0 : Fin 6)) (.bound (1 : Fin 6)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem difference_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence differenceSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) differenceSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    value_semantics hM,ConstructionCutAddition.sumCut_semantics hM,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff]
  intro hw hQ ha hb hab
  obtain ⟨gap,hgap,hValue,hSum,_,hPositive⟩ := exists_difference hM hw hQ ha hb hab
  exact ⟨gap,hgap,hValue,hSum,fun _ hg hs => difference_solution_unique hM hw hQ ha hg hgap hs hSum,hPositive⟩

theorem difference_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence differenceSentence) := ModelTransfer.derives (fun _ hM => difference_models hM)

def orderSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 7))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    7) 1) (.imp (ConstructionRealCuts.cut (0 : Fin 7) 1 2) (.imp (ConstructionRealCuts.cut (0 : Fin 7) 1
    3) (.imp (ConstructionRealCuts.cut (0 : Fin 7) 1 4) (.imp (ConstructionCutAddition.sumCut (0 : Fin 7)
    1 2 4 5) (.imp (ConstructionCutAddition.sumCut (0 : Fin 7) 1 3 4 6) (.conj (.iff
    (Project.Formula.subset (.bound (5 : Fin 7)) (.bound (6 : Fin 7))) (Project.Formula.subset (.bound (2
    : Fin 7)) (.bound (3 : Fin 7)))) (.conj (.imp (Project.Formula.extensionalEq (.bound (5 : Fin 7))
    (.bound (6 : Fin 7))) (Project.Formula.extensionalEq (.bound (2 : Fin 7)) (.bound (3 : Fin 7)))) (.iff
    (.conj (Project.Formula.subset (.bound (5 : Fin 7)) (.bound (6 : Fin 7))) (.neg
    (Project.Formula.subset (.bound (6 : Fin 7)) (.bound (5 : Fin 7))))) (.conj (Project.Formula.subset
    (.bound (2 : Fin 7)) (.bound (3 : Fin 7))) (.neg (Project.Formula.subset (.bound (3 : Fin 7)) (.bound
    (2 : Fin 7)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem order_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence orderSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) orderSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    ConstructionCutAddition.sumCut_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_neg_iff]
  intro hw hQ ha hb hc hac hbc
  exact ⟨sum_le_iff hM hw hQ ha hb hc hac hbc,
    fun he => sum_cancel hM hw hQ ha hb hc hac hbc he,sum_strict_iff hM hw hQ ha hb hc hac hbc⟩

theorem order_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence orderSentence) := ModelTransfer.derives (fun _ hM => order_models hM)

end PPAC.Migration.ConstructionCutDifferenceSyntax
