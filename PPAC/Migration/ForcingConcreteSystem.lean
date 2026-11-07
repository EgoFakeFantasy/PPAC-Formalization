/- Fixed ConcreteSystem: assemble ONE actual internal weighted saturation
history and forcing/label system. Preserve the existing hRec/hMatrix/final row;
reuse Base/Tower, native Hartogs/identity, product, group/filter and label-bound
constructors. No concrete-system hypothesis remains in the existence theorem. -/
import PPAC.Migration.ForcingNonwellorderableQuotient
import PPAC.Migration.ConstructionConcreteBase

namespace PPAC.Migration.ForcingConcreteSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductFamily (actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingMapConditions (MapRel)
open ForcingSupportSize (Injection Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private def rho : Fin 7 → Fin 40 := Fin.cases 17 (Fin.cases 28 (Fin.cases 29 (Fin.cases 30 (Fin.cases 31 (Fin.cases 32 (fun _ => 33))))))

private def frame (w seedMul zero high B three Q values seedH seedC u groundTop Power continuum mu K stageBound history D mul one mark H C incoming base P outerF I CC CS X Y Product W G F labelMap labels bound : M.Carrier .set) : Fin 40 → M.Carrier .set :=
  Fin.cases seedMul (Fin.cases zero (Fin.cases high (Fin.cases B (Fin.cases three (Fin.cases Q (Fin.cases values (Fin.cases seedH (Fin.cases seedC (Fin.cases u (Fin.cases groundTop (Fin.cases Power (Fin.cases continuum (Fin.cases mu (Fin.cases K (Fin.cases stageBound (Fin.cases history (Fin.cases D (Fin.cases mul (Fin.cases one (Fin.cases mark (Fin.cases H (Fin.cases C (Fin.cases incoming (Fin.cases base (Fin.cases P (Fin.cases outerF (Fin.cases I (Fin.cases CC (Fin.cases CS (Fin.cases X (Fin.cases Y (Fin.cases Product (Fin.cases W (Fin.cases G (Fin.cases F (Fin.cases labelMap (Fin.cases labels (Fin.cases bound (Fin.cases w Fin.elim0)))))))))))))))))))))))))))))))))))))))

def Core (hM : FirstOrder.Theory.Models M nativeZF) (env : Fin 40 → M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).IsOrdinal (env 14)) ∧
  (ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env 18) (env 19)) ∧
  (ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env 18)) ∧
  (ForcingProductFamily.Presentation (env (rho 0)) (env 27) (env 14) (env 3) (env 39) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6))) ∧
  (ForcingLabelPermutations.Carrier (env 27) (env 34)) ∧
  (ForcingSupportFilter.Filter (env 27) (env 34) (env 13) (env 35)) ∧
  ((Project.FirstOrderSemantics.reduct M).IsOmega (env 39)) ∧
  ((Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env 39) (env 13)) ∧
  ((Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env 27) (env 13)) ∧
  (ForcingSupportSize.Small (env (rho 0)) (env 13)) ∧
  (ConstructionSaturationMergers.AllMergers (env 39) (env 16) (env 14)) ∧
  (ConstructionTowerHistory.Row (env 16) (env 14) (env (rho 0)) (env 18) (env 19) (env 20) (env 21) (env 22) (env 23) (env 24) (env 14)) ∧
  (ForcingConditionGraphs.FunctionOn (env 14) (env 36)) ∧
  (ForcingWithTopCarrier.Empty (env 1)) ∧
  (ForcingLabelSet.LabelSet (env (rho 6)) (env 27) (env 14) (env 36) (env 1) (env 2) (env 37)) ∧
  (ForcingLabelBound.LabelBound (env (rho 6)) (env 27) (env 14) (env 36) (env 1) (env 2) (env 38)) ∧
  (ConstructionRoundFields.ObjectFields hM (env 39) (env 5) (env 6) (env 10) (env (rho 0)) (env 18) (env 19) (env 20) (env 21) (env 22)) ∧
  ((Project.FirstOrderSemantics.reduct M).mem (env 20) (env (rho 0))) ∧
  (ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env 18) (env 20) (env 13)) ∧
  (¬ ForcingSupportSize.Small (env 14) (env 39)) ∧
  (Injection (env 14) (env 14) (env 36)) ∧
  ((Project.FirstOrderSemantics.reduct M).mem (env 1) (env 3)) ∧
  ((Project.FirstOrderSemantics.reduct M).mem (env 2) (env 3)) ∧
  ((Project.FirstOrderSemantics.reduct M).SuccessorOf (env 3) (env 2)) ∧
  (env 1 ≠ env 2) ∧
  (∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env 3) o) ∧
  ((Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env 14) (env 13)) ∧
  (ConstructionConcreteCardinals.Parameters hM (env 39) (env 11) (env 12) (env 13)) ∧
  (ConstructionIdealProbes.AllIdeals (env 13) (env 16) (env 14)) ∧
  (ForcingSupportedNames.Supported (fun j => env (rho j)) (env 34) (env 38)) ∧
  (ConstructionSaturationIterationCases.Context hM (env 39) (env 5) (env 6) (env 10) (env 39) (env 0) (env 1) (env 2) (env 7) (env 8) (env 1) (env 2) (env 9) (env 13) (env 13) (env 15)) ∧
  (ConstructionSaturationIteration.Recursive hM (env 39) (env 5) (env 6) (env 10) (env 39) (env 0) (env 1) (env 2) (env 7) (env 8) (env 1) (env 2) (env 13) (env 13) (env 15) (env 15) (env 16)) ∧
  (ConstructionSaturationIndex.Data hM (env 39) (env 13) (env 14) (env 15)) ∧
  (ConstructionTowerTransitions.Matrix (env 15) (env 16) (env 1) (env 25) (env 26)) ∧
  ((Project.FirstOrderSemantics.reduct M).SuccessorOf (env 2) (env 1)) ∧
  (ForcingCohenCoordinates.Cartesian (env 27) (env 14) (env (rho 1))) ∧
  (ForcingCohenCoordinates.Cartesian (env (rho 1)) (env 3) (env (rho 2)))


theorem construct_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ bound labels labelMap F G W Product Y X CS CC I outerF P base incoming C H mark one mul D history stageBound K mu continuum Power groundTop u seedC seedH values Q three B high zero seedMul, Core hM (frame w seedMul zero high B three Q values seedH seedC u groundTop Power continuum mu K stageBound history D mul one mark H C incoming base P outerF I CC CS X Y Product W G F labelMap labels bound) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨seedMul,zero,high,B,three,Q,values,seedH,seedC,u,groundTop,Power,continuum,mu,K,stageBound,hData⟩ :=
    ConstructionConcreteBase.exists_tower_data hM hOrder hChoice hw
  have hBase := hData.1
  have hParameters := hData.2.1
  have hIdeal := hData.2.2
  have hCardinalTower := hIdeal.1
  have hComplementTower := hCardinalTower.1
  have hMergerTower := hComplementTower.1
  have hProbeTower := hMergerTower.1
  have hIndexTower := hProbeTower.1.1
  have hIndex := hIndexTower.1
  have hctx := hIndexTower.2.1
  obtain ⟨history,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,outerF,
    hrec,hValid,_,_,_,_,hf,_,_⟩ := hIndexTower.2.2
  have hKLast := hIndex.2.2.2.1.predecessor_mem
  obtain ⟨D,mul,one,mark,H,C,incoming,base,hRow⟩ := hValid.1.2 K hKLast
  have hObj := (hValid.2.1 K hKLast D mul one mark H C incoming base hRow).1
  have hMergers := hMergerTower.2 history P outerF hrec hf
  have hAllIdeals := hIdeal.2 history P outerF hrec hf
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_identityBijection hZF pair mu
  have hCard := hCardinalTower.2 ⟨idMu,hIdMu⟩ history P outerF hrec hf D mul one mark H C incoming base hRow
  have hMu := hctx.2.2.2.2.2.2.2.2.2.2.1
  have hSmallW : Small w mu := (ForcingSupportSize.native_small hM _ _).mpr hMu.2
  obtain ⟨dm,hdm⟩ := hCard.1
  have hSmallD : Small D mu := (ForcingSupportSize.native_small hM _ _).mpr ⟨dm,hdm.1⟩
  obtain ⟨I,hI⟩ := ExistingOrdinalEnumeration.exists_hartogsNumber_kernel hZF pair mu
  have hK := hIndex.1.1
  have hUncountable : ¬ Small K w := fun h =>
    hIndex.1.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  have hKLeMu := (ForcingSupportSize.native_small hM K mu).mp hIndex.2.2.2.2.2.1
  have hZero := hctx.2.2.2.2.2.2.2.1
  have hHighOne := hctx.2.2.2.2.1
  obtain ⟨z,hz,hHighSucc⟩ := hHighOne
  have hZeroEq : z = zero := hZF.1.eq_of_same_members z zero (fun x => iff_of_false (hz x) (hZero x))
  subst z
  have hDigits := hBase.1.2.2.2.2.2.2.1
  have hBitSuccessor := hDigits.2.2.2.2.1
  have hHighOne' : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne high := ⟨zero,hZero,hHighSucc⟩
  have hBOrdinal := KP.successor_isOrdinal (ZF.modelsKP hZF)
    (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hHighOne') hBitSuccessor
  have hBit := hBitSuccessor.predecessor_mem
  have hLo := hBOrdinal.transitive high hBit zero hHighSucc.predecessor_mem
  have hBits : zero ≠ high := Ne.symm hBase.1.2.2.2.2.1
  obtain ⟨CC,CS,X,Y,Product,W,hPres⟩ := ForcingProductFamily.exists_presentation hM D I K B w
  obtain ⟨G,hG⟩ := ForcingLabelPermutations.exists_carrier hM I
  obtain ⟨F,hF⟩ := ForcingSupportFilter.exists_filter hM I G mu
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  obtain ⟨labelMap,hLabelId⟩ := ZF.exists_identityBijection hZF pair K
  have hCoding := (ForcingSupportSize.native_injection hM K K labelMap).mpr hLabelId.1
  have hLabelMap := hCoding.1.1
  have hTopW := (hPres.2.2.2.2.2 zero).mpr (Or.inl hZero)
  obtain ⟨labels,hLabels⟩ := ForcingLabelSet.exists_labelSet hM hLabelMap hTopW I high
  let v : Fin 7 → M.Carrier .set := Fin.cases D (Fin.cases CC (Fin.cases CS (Fin.cases X (Fin.cases Y (Fin.cases Product (fun _ => W))))))
  obtain ⟨hLabelsHS,hLabelsFixed⟩ := ForcingLabelSet.HS_and_fixed hM v
    hPres hG hNormal hF hw hSmallW hLabelMap hZero hLabels
  obtain ⟨stabilizer,bound,hStabilizer,_,_,hBoundRaw,hBoundFixed⟩ := ForcingPowerName.exists_bound hM v hPres hG hLabelsHS
  have hLabelBound := (ForcingLabelBound.bound_iff hM hLabels).mp hBoundRaw
  have hBound : ForcingSupportedNames.Supported v G bound := by
    intro pi hpi a ha
    exact hBoundFixed pi ((hStabilizer pi).mpr ⟨hpi,a,ha,hLabelsFixed pi hpi a ha⟩) a ha
  exact ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,⟨hK,hObj.1,hObj.2.2.1,hPres,hG,hF,hw,hMu,hI,hSmallD,hMergers,hRow,hLabelMap,hZero,hLabels,hLabelBound,hObj,hObj.2.2.2.1,hCard,hUncountable,hCoding,hLo,hBit,hBitSuccessor,hBits,⟨high,hHighOne',hBitSuccessor⟩,hKLeMu,hParameters,hAllIdeals,hBound,hctx,hrec,hIndex,hf,hHighSucc,hPres.1,hPres.2.1⟩⟩

def Outcome (env : Fin 40 → M.Carrier .set) : Prop :=
  ∀ E name initial,
    let other : Fin 43 → M.Carrier .set := Fin.cases initial (Fin.cases name (Fin.cases E env))
    let up : Fin 40 → Fin 43 := fun j => j.succ.succ.succ
    ForcingHS.HS actionFormula (fun j => env (rho j)) (env 34) (env 33) (env 35) E →
    ForcingQuotientName.Quotient other (fun j => up (rho j)) (up 34) (up 35) (up 18) (up 27) (up 14)
      (up 36) (up 1) (up 2) (up 37) 2 name →
    (Project.FirstOrderSemantics.reduct M).mem initial (env 33) →
    ForcingFormula.Force (orderFormula (up (rho 0)) (up 18))
      (ForcingPairUnion.domain (fun j => up (rho j)) (up 34) (up 35)) other
      (Source.SetLanguage.args1 name) (env 33) initial (ForcingCheckOrdinal.wellorderable 0).neg →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env 33) ∧
      MapRel (orderFormula (up (rho 0)) (up 18)) other r initial ∧
      ∃ graph, ForcingHS.HS actionFormula (fun j => env (rho j)) (env 34) (env 33) (env 35) graph ∧
        ForcingFormula.Force (orderFormula (up (rho 0)) (up 18))
          (ForcingPairUnion.domain (fun j => up (rho j)) (up 34) (up 35)) other
          (Source.SetLanguage.args3 graph (env 37) name) (env 33) r
          ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))

theorem consequences (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin 40 → M.Carrier .set) (hCore : Core hM env) : Outcome env := by
  obtain ⟨hK,hm,hJ,hp,hG,hF,hw,hMu,hI,hSmallD,hMergers,hRow,hLabelMap,hTop,hLabels,hLabelBound,hObjFields,hMark,hCard,hUncountable,hCoding,hLo,hBit,hBitSuccessor,hBits,hTwo,hKLeMu,hParameters,hAllIdeals,hBound,hctx,hrec,hindex,hf,hHigh,hCoords,hSpace⟩ := hCore
  intro E name initial
  dsimp only
  intro hEHS hName hInitial hNot
  let other : Fin 43 → M.Carrier .set := Fin.cases initial (Fin.cases name (Fin.cases E env))
  let up : Fin 40 → Fin 43 := fun j => j.succ.succ.succ
  exact ForcingNonwellorderableQuotient.nonwellorderable hM hOrder hChoice other (fun j => up (rho j))
    (up 27) (up 14) (up 3) (up 39) (up 34) (up 35) (up 18) (up 19) (up 13) (up 16) (up 20) (up 21) (up 22) (up 23) (up 24) (up 36) (up 1) (up 2) (up 37) 2 (up 38) (up 1) (up 2) (up 5) (up 6) (up 10) (up 0) (up 1) (up 2) (up 7) (up 8) (up 2) (up 9) (up 13) (up 15) (up 25) (up 26) 1 (up 14) (up 1) (up 11) (up 12) 0
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hObjFields hMark hCard hEHS hName hUncountable hCoding hLo hBit hBitSuccessor hBits hTwo hKLeMu hParameters hAllIdeals hBound hctx hrec hindex hf hHigh hCoords hSpace hInitial hNot

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ bound labels labelMap F G W Product Y X CS CC I outerF P base incoming C H mark one mul D history stageBound K mu continuum Power groundTop u seedC seedH values Q three B high zero seedMul,
      Core hM (frame w seedMul zero high B three Q values seedH seedC u groundTop Power continuum mu K stageBound history D mul one mark H C incoming base P outerF I CC CS X Y Product W G F labelMap labels bound) ∧ Outcome (frame w seedMul zero high B three Q values seedH seedC u groundTop Power continuum mu K stageBound history D mul one mark H C incoming base P outerF I CC CS X Y Product W G F labelMap labels bound) := by
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore⟩ := construct_core hM hOrder hChoice hw
  exact ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,consequences hM hOrder hChoice _ hCore⟩

def coreFormula : Project.Formula 1 40 :=
  (.conj (Project.Formula.isOrdinal (.bound 14))
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) 18 19))
    (.conj (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) 18)
    (.conj (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) 27 14 3 39 (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.carrier 27 34))
    (.conj (ProjectSyntax.encode id (ForcingSupportFilter.filter 27 34 13 35))
    (.conj (Project.Formula.isOmega (.bound 39))
    (.conj (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 39) (.bound 13))
    (.conj (ConstructionSaturationIndex.hartogs 13 27)
    (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) 13))
    (.conj (ConstructionSaturationMergers.allMergers 39 16 14)
    (.conj (ConstructionTowerHistory.row 16 14 (rho 0) 18 19 20 21 22 23 24 14)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn 36 14))
    (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty 1))
    (.conj (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) 27 14 36 1 2 37))
    (.conj (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) 27 14 36 1 2 38))
    (.conj (ConstructionRoundStepSyntax.objectFields 39 5 6 10 (rho 0) 18 19 20 21 22)
    (.conj (.mem (.bound 20) (.bound (rho 0)))
    (.conj (ConstructionSaturationCardinals.cardinalsF (rho 0) 18 20 13)
    (.conj (.neg (ProjectSyntax.encode id (ForcingSupportSize.small 14 39)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 36 14 14))
    (.conj (.mem (.bound 1) (.bound 3))
    (.conj (.mem (.bound 2) (.bound 3))
    (.conj (Project.Formula.isSuccessor (.bound 3) (.bound 2))
    (.conj (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 2)))
    (.conj (ForcingProductParameters.two 3)
    (.conj (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 14) (.bound 13))
    (.conj (ConstructionConcreteCardinals.parameters 39 11 12 13)
    (.conj (ConstructionIdealProbes.allIdeals 13 16 14)
    (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho 34 38))
    (.conj (ConstructionSaturationIterationCases.context 39 5 6 10 39 0 1 2 7 8 1 2 9 13 13 15)
    (.conj (ConstructionSaturationIteration.recursive 39 5 6 10 39 0 1 2 7 8 1 2 13 13 15 15 16)
    (.conj (ConstructionSaturationIndex.data 39 13 14 15)
    (.conj (ConstructionTowerTransitions.matrix 15 16 1 25 26)
    (.conj (Project.Formula.isSuccessor (.bound 2) (.bound 1))
    (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian 27 14 (rho 1)))
    (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 1) 3 (rho 2)))))))))))))))))))))))))))))))))))))))

theorem coreFormula_freeClosed : coreFormula.FreeClosed := by
  simp -implicitDefEqProofs [coreFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,Project.Formula.extensionalEq,
      ForcingProductParameters.two_freeClosed,ConstructionConcreteCardinals.parameters_freeClosed,
      ConstructionIdealProbes.allIdeals_freeClosed,ConstructionSaturationIterationCases.context_freeClosed,
      ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,Project.Formula.isSuccessor]

theorem coreFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env coreFormula ↔ Core hM env.bound := by
  simp only [coreFormula,Core,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOrdinal_iff,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),
    ConstructionRoundStepSyntax.objectFields_semantics hM,
    Project.Formula.satisfies_mem_iff,
    ConstructionSaturationCardinals.cardinalsF_semantics hM,
    Project.Formula.satisfies_neg_iff,
    ForcingSupportSize.injection_semantics (M := M),
    Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ForcingProductParameters.two_semantics (M := M),
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionConcreteCardinals.parameters_semantics hM,
    ConstructionIdealProbes.allIdeals_semantics hM,
    ForcingSupportedNames.supported_semantics (M := M),
    ConstructionSaturationIterationCases.context_semantics hM,
    ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,
    ForcingCohenCoordinates.cartesian_semantics (M := M),
    id_eq]

def outcomeFormula : Project.Formula 1 40 :=
  let up : Fin 40 → Fin 43 := fun j => j.succ.succ.succ
  let r : Fin 7 → Fin 43 := fun j => up (rho j)
  .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula r (up 34) (up 33) (up 35) 2))
    (.imp (ProjectSyntax.encode id (ForcingQuotientName.quotient r (up 34) (up 35) (up 18) (up 27) (up 14)
      (up 36) (up 1) (up 2) (up 37) 2 id 1))
    (.imp (.mem (.bound 0) (.bound (up 33)))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (up (rho 0)) (up 18))
      (ForcingPairUnion.domain r (up 34) (up 35)) id (Source.SetLanguage.args1 1) (up 33) 0 (ForcingCheckOrdinal.wellorderable 0).neg))
      (ForcingNonwellorderableQuotient.result r (up 34) (up 35) (up 18) (up 37) 1 0)))))))

theorem outcomeFormula_freeClosed : outcomeFormula.FreeClosed := by
  simp -implicitDefEqProofs [outcomeFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingNonwellorderableQuotient.result_freeClosed]

private theorem args3_map {n : Nat} (f : Fin n → M.Carrier .set) (a b c : Fin n) :
    (fun j => f (Source.SetLanguage.args3 a b c j)) = Source.SetLanguage.args3 (f a) (f b) (f c) := by
  funext j
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.elim0 j) j) j) j

theorem outcomeFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env outcomeFormula ↔ Outcome env.bound := by
  simp only [outcomeFormula,Outcome,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ForcingFormula.formula_semantics (M := M),ForcingNonwellorderableQuotient.result,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingMapConditions.rel_semantics (M := M),args3_map,id_eq]
  rfl

def sentence : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj coreFormula outcomeFormula)))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,coreFormula_freeClosed,outcomeFormula_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) sentence.formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩ := construct hM hOrder hChoice hw
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coreFormula_semantics hM,outcomeFormula_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩

theorem kernel_certificate :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sentence)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence)).mp
      (models hL (ConstructionRoundSelection.l_order hM) hChoice)





/-- Existing literal source forcing frame, exposed for same-system consumers. -/
def forcingRho : Fin 7 → Fin 40 := rho

end PPAC.Migration.ForcingConcreteSystem
