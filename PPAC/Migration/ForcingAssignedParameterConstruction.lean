/- Fixed OrbitAssignments.Assigned: compose actual whole-orbit record construction
with all sixteen native projections. No assumed auxiliary record/function family
remains in this constructor; the original common parent-system guards are retained. -/
import PPAC.Migration.ForcingAssignedParameters

namespace PPAC.Migration.ForcingAssignedParameterConstruction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env K))
    (hRow : ConstructionTowerHistory.Row (env history) (env K) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env K))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : ForcingSupportSize.MapsTo (env diagrams) (env objImage) (env objects))
    (hctx : ConstructionSaturationIterationCases.Context hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env u) (env seedK) (env mu) (env stageBound))
    (hrec : ConstructionSaturationIteration.Recursive hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env seedK) (env mu) (env stageBound) (env stageBound) (env history))
    (hindex : ConstructionSaturationIndex.Data hM (env w) (env mu) (env K) (env stageBound))
    (hf : ConstructionTowerTransitions.Matrix (env stageBound) (env history) (env zero) (env P) (env outerF))
    (hHigh : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env high) (env zero))
    (hBits : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) (env high))
    (hCoords : ForcingCohenCoordinates.Cartesian (env I) (env K) (env (rho 1)))
    (hSpace : ForcingCohenCoordinates.Cartesian (env (rho 1)) (env B) (env (rho 2)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env orbitQuotient) (env reps) (env chains))
    (hReps : ForcingConditionGraphs.FunctionOn (env orbitQuotient) (env reps)) :
    ∃ records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders,
      ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records ∧
      ForcingAssignedParameters.Projections (env high) (env orbitQuotient) records (env reps) (env chains) Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders ∧
      ForcingAssigned.Germs (env (rho 0)) (env I) (env mul) (env q) (env reps) Germs := by
  obtain ⟨records,hFamily⟩ := ForcingOrbitParameterFamily.construct hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains
    hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE
    hVertices hDiagrams hObj hctx hrec hindex hf hHigh hBits hCoords hSpace hChains
  obtain ⟨Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hProjections,hGerms⟩ := ForcingAssignedParameters.construct hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily hReps hChains.1
  exact ⟨records,Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hFamily,hProjections,hGerms⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+15) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history K)
    (.imp (ConstructionTowerHistory.row history K (rho 0) mul one mark H C incoming base K)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ConstructionSaturationIterationCases.context w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne u seedK mu stageBound)
    (.imp (ConstructionSaturationIteration.recursive w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne seedK mu stageBound stageBound history)
    (.imp (ConstructionSaturationIndex.data w mu K stageBound)
    (.imp (ConstructionTowerTransitions.matrix stageBound history zero P outerF)
    (.imp (Project.Formula.isSuccessor (.bound high) (.bound zero))
    (.imp (Project.Formula.isSuccessor (.bound B) (.bound high))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K (rho 1)))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 1) B (rho 2)))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices orbitQuotient reps chains)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn reps orbitQuotient))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (ForcingOrbitParameterFamily.family rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient up 14)
      (.conj (ForcingAssignedParameters.projections (up high) (up orbitQuotient) 14 (up reps) (up chains) 13 12 11 10 9 8 7 6 5 4 3 2 1 0)
        (ForcingAssigned.germs (up (rho 0)) (up I) (up mul) (up q) (up reps) 5)))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      Project.Formula.isSuccessor,ForcingOrbitParameterFamily.family_freeClosed,ForcingOrbitChains.family_freeClosed,
      ForcingAssignedParameters.projections_freeClosed,ForcingAssigned.germs_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,ForcingOrbitChains.family_semantics hM,
    Project.Formula.satisfies_conj_iff,ForcingAssignedParameters.projections_semantics hM,ForcingAssigned.germs_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    Project.Formula.satisfies_isSuccessor_iff,ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construct hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains)).mp
      (construction_models rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF orbitQuotient reps chains hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ForcingAssignedParameterConstruction
