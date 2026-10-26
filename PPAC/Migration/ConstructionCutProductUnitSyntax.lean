/- Pure native-ZF unit law for the actual cut product used by source bounds. -/
import PPAC.Migration.ConstructionCutProductUnit

namespace PPAC.Migration.ConstructionCutProductUnitSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 6))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 6) (1 :
Fin 6)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 6) (3 : Fin 6) (2 : Fin 6) (2 : Fin 6)) (.imp
(Project.Formula.isOrdinalOne (.bound (2 : Fin 6))) (.imp (ConstructionRealCuts.principal (0 : Fin 6) (1 : Fin
6) (3 : Fin 6) (4 : Fin 6)) (.imp (ConstructionRealCuts.cut (0 : Fin 6) (1 : Fin 6) (5 : Fin 6)) (.conj
(ConstructionCutProduct.value (0 : Fin 6) (1 : Fin 6) (5 : Fin 6) (4 : Fin 6) (5 : Fin 6)) (.forallE (.forallE
(.imp (ConstructionCutProduct.value (2 : Fin 8) (3 : Fin 8) (7 : Fin 8) (1 : Fin 8) (0 : Fin 8)) (.imp
(Project.Formula.subset (.bound (1 : Fin 8)) (.bound (6 : Fin 8))) (Project.Formula.subset (.bound (0 : Fin 8))
(.bound (7 : Fin 8))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.principal_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionCutProduct.value_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Term.eval_bound,
    ConstructionRealCuts.principal_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionCutProduct.value_semantics hM,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_subset_iff]
  intro hw hQ hu hone hunit ha
  exact ⟨ConstructionCutProductUnit.right_unit hM hw hQ hu hone hunit ha,
    fun _ _ hc hb => ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit ha hc hb⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionCutProductUnitSyntax
