/- Consume the existing concrete selector construction in the SAME fixed
Cohen presentation used by OrbitAssignments and AssignedGraphs. Literal one/two
and Cartesian carriers are aligned by extensional uniqueness; no new selector. -/
import PPAC.Migration.ConstructionConcreteSelector

namespace PPAC.Migration.ConstructionSelectorPresentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConcreteSelector (Result resultFormula resultFormula_freeClosed resultFormula_semantics)
open ConstructionTowerHistory (Row)
open ForcingSupportSize (Injection)
open ForcingCohenCoordinates (Cartesian)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem construction_in_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top w mul unit mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top w mul unit mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V GV e markV HV CV terminalLegs baseV kappa)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : ConstructionComponentCofinal.Chain w V labels GV q zero root vertices chain)
    (hq : Injection V labels q)
    (hHigh : (Project.FirstOrderSemantics.reduct M).SuccessorOf high zero)
    (hBits : (Project.FirstOrderSemantics.reduct M).SuccessorOf bits high)
    (hCoords : Cartesian labels kappa coords) (hSpace : Cartesian coords bits space) :
    ∃ group quotient projection reps N X det J O order Psel f,
      Result hM w V labels GV q root chain kappa zero group quotient projection reps N X det J high bits coords space O order Psel f := by
  obtain ⟨group,quotient,projection,reps,N,X,det,J,hi,bits',coords',space',O,order,Psel,f,hResult⟩ :=
    ConstructionConcreteSelector.construction hM hOrder hChoice hctx hrec hindex hf hr hX hC hq
  have hResultCopy := hResult
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hhi,hbits,hcoords,hspace,_⟩ := hResultCopy
  have eHigh : hi = high := (ModelTransfer.extensionality hM).eq_of_same_members hi high
    (fun z => (hhi z).trans (hHigh z).symm)
  have eBits : bits' = bits := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    have aligned : (Project.FirstOrderSemantics.reduct M).SuccessorOf bits' high := eHigh ▸ hbits
    exact (aligned z).trans (hBits z).symm
  have eCoords : coords' = coords := (ModelTransfer.extensionality hM).eq_of_same_members coords' coords
    (fun z => (hcoords z).trans (hCoords z).symm)
  have eSpace : space' = space := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    have aligned : Cartesian coords bits space' := by simpa only [eCoords,eBits] using hspace
    exact (aligned z).trans (hSpace z).symm
  refine ⟨group,quotient,projection,reps,N,X,det,J,O,order,Psel,f,?_⟩
  simpa only [eHigh,eBits,eCoords,eSpace] using hResult

def constructionSentence {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space : Fin m) : Project.Sentence where
  formula :=
    let up : Fin m → Fin (m+12) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Project.Formula.forallClosure m (.imp (ConstructionSaturationIterationCases.context w Q values top w mul unit mark H C zero one u K mu B)
    (.imp (ConstructionSaturationIteration.recursive w Q values top w mul unit mark H C zero one K mu B B history)
    (.imp (ConstructionSaturationIndex.data w mu kappa B)
    (.imp (ConstructionTowerTransitions.matrix B history zero P outerF)
    (.imp (ConstructionTowerHistory.row history kappa V GV e markV HV CV terminalLegs baseV kappa)
    (.imp (ConstructionComponentCarrier.carrier V labels GV q vertices)
    (.imp (ConstructionComponentCofinal.chain w V labels GV q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q V labels))
    (.imp (Project.Formula.isSuccessor (.bound high) (.bound zero))
    (.imp (Project.Formula.isSuccessor (.bound bits) (.bound high))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian labels kappa coords))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coords bits space))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (resultFormula (up w) (up V) (up labels) (up GV) (up q) (up root) (up chain) (up kappa) (up zero) 11 10 9 8 7 6 5 4 (up high) (up bits) (up coords) (up space) 3 2 1 0)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,resultFormula_freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,Project.Formula.isSuccessor]

theorem construction_models {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),resultFormula_semantics hM,
    ConstructionSaturationIterationCases.context_semantics hM,
    ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construction_in_presentation hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space)).mp (construction_models w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain high bits coords space hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ConstructionSelectorPresentation
