/- Pure native-ZF associativity certificate for the actual cut addition used
by the pinned ProbeMargins interval and height computations. -/
import PPAC.Migration.ConstructionCutAssociativity

namespace PPAC.Migration.ConstructionCutAssociativitySyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCutAssociativity
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def associativitySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 9
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 9))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    9) (1 : Fin 9)) (.imp (ConstructionRealCuts.cut (0 : Fin 9) (1 : Fin 9) (2 : Fin 9)) (.imp
    (ConstructionRealCuts.cut (0 : Fin 9) (1 : Fin 9) (3 : Fin 9)) (.imp (ConstructionRealCuts.cut (0 :
    Fin 9) (1 : Fin 9) (4 : Fin 9)) (.imp (ConstructionCutAddition.sumCut (0 : Fin 9) (1 : Fin 9) (2 : Fin
    9) (3 : Fin 9) (5 : Fin 9)) (.imp (ConstructionCutAddition.sumCut (0 : Fin 9) (1 : Fin 9) (3 : Fin 9)
    (4 : Fin 9) (6 : Fin 9)) (.imp (ConstructionCutAddition.sumCut (0 : Fin 9) (1 : Fin 9) (5 : Fin 9) (4
    : Fin 9) (7 : Fin 9)) (.imp (ConstructionCutAddition.sumCut (0 : Fin 9) (1 : Fin 9) (2 : Fin 9) (6 :
    Fin 9) (8 : Fin 9)) (Project.Formula.extensionalEq (.bound (7 : Fin 9)) (.bound (8 : Fin 9))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem associativity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence associativitySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) associativitySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionCutAddition.sumCut_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact cut_assoc hM

theorem associativity_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence associativitySentence) := ModelTransfer.derives (fun _ hM => associativity_models hM)

end PPAC.Migration.ConstructionCutAssociativitySyntax
