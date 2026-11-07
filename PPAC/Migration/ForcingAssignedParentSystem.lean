/- Shared root parents for the pinned ConcreteQuotients quotient-bijection route.
Construct the label system, complete candidate/vertex carriers, orbit quotient,
representatives and chains, then reuse the EXISTING whole-orbit parameter
constructor. Every generated object is an internal set; no assumed record family. -/
import PPAC.Migration.ForcingAssignedParameterConstruction
import PPAC.Migration.ForcingConcreteLabels

namespace PPAC.Migration.ForcingAssignedParentSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private def up {k : Nat} (j : Fin k) : Fin (k+12) := j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

private def frame {α : Type u} {k : Nat} (env : Fin k → α)
    (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains : α) : Fin (k+12) → α :=
  Fin.cases vertices (Fin.cases names (Fin.cases diagrams (Fin.cases objImage (Fin.cases objects (Fin.cases arrows (Fin.cases mapImage (Fin.cases maps (Fin.cases orbitQuotient (Fin.cases pr (Fin.cases reps (Fin.cases chains (env))))))))))))

def Parents (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero high : Fin k)
    (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : M.Carrier .set) : Prop :=
  let localEnv := frame env vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains
  ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) diagrams ∧
  ForcingSupportSize.MapsTo diagrams objImage objects ∧
  ForcingLabelSystem.Objects (env (rho 0)) diagrams objects ∧
  ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) diagrams arrows ∧
  ForcingSupportSize.MapsTo arrows mapImage maps ∧
  ForcingLabelSystem.Maps objects arrows maps ∧
  ForcingEligibleSystem.System (env (rho 0)) objects maps ∧
  ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) objects maps ∧
  ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) vertices ∧
  ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) names ∧
  ForcingSupportSize.MapsTo vertices orbitQuotient pr ∧
  ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) vertices orbitQuotient ∧
  ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) vertices pr ∧
  ConstructionGermDetectors.Representatives vertices orbitQuotient reps ∧
  ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) vertices orbitQuotient reps chains ∧
  ForcingOrbitParameterFamily.Family hM localEnv (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up zero) 1 (up high) 4 7 10 11 8 records ∧
  ForcingAssignedParameters.Projections (env high) orbitQuotient records reps chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders ∧
  ForcingAssigned.Germs (env (rho 0)) (env I) (env mul) (env q) reps Germs

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k)
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
    (hctx : ConstructionSaturationIterationCases.Context hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env u) (env seedK) (env mu) (env stageBound))
    (hrec : ConstructionSaturationIteration.Recursive hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env seedK) (env mu) (env stageBound) (env stageBound) (env history))
    (hindex : ConstructionSaturationIndex.Data hM (env w) (env mu) (env K) (env stageBound))
    (hf : ConstructionTowerTransitions.Matrix (env stageBound) (env history) (env zero) (env P) (env outerF))
    (hHigh : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env high) (env zero))
    (hBits : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) (env high))
    (hCoords : ForcingCohenCoordinates.Cartesian (env I) (env K) (env (rho 1)))
    (hSpace : ForcingCohenCoordinates.Cartesian (env (rho 1)) (env B) (env (rho 2)))
    (hObject : ConstructionRoundFields.ObjectFields hM (env w) (env Q) (env values) (env groundTop) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C)) :
    ∃ vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders,
      Parents hM env rho I K B w G F mul q bound labels E zero high vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders := by
  obtain ⟨diagrams,objImage,objects,arrows,mapImage,maps,hDiagrams,hObj,hObjects,hArrows,hMaps,hMapFamily,hSystem⟩ :=
    ForcingLabelSystem.exists_system hM (env (rho 0)) (env I) (env mul)
  have hCommon := ForcingConcreteLabels.common_fibers hM hm hJ hDiagrams hObj hArrows hMaps hMapFamily hSystem
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (env (rho 0)) (env I) (env mul) (env q)
  obtain ⟨names,hNames⟩ := ForcingPowerName.exists_candidates hM (fun j => env (rho j)) (env G) (env F) (env bound)
  obtain ⟨orbitQuotient,pr,hpr,hQuotient,hProjection⟩ :=
    ForcingOrbitQuotient.exists_quotient hM (env (rho 0)) (env I) (env mul) (env q) vertices
  obtain ⟨reps,hReps⟩ := ForcingOrbitRepresentatives.exists_representatives hM hChoice hm hq hVertices hQuotient
  have hQ := hctx.2.1
  have hR := hctx.2.2.1
  have huQ := (hQ (env u)).mpr ⟨env ordinalOne,env ordinalOne,hctx.2.2.2.1⟩
  have hCut := ConstructionRealCuts.principal_cut hM hw hQ huQ hctx.2.2.2.2.2.1
  obtain ⟨chains,hChains⟩ := ForcingOrbitChains.exists_family hM hChoice hw hQ hR hCut hObject hVertices hctx.2.2.2.2.2.2.2.1 hReps
  let localEnv : Fin (k+12) → M.Carrier .set := frame env vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains
  obtain ⟨records,Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hRecords,hProjections,hGerms⟩ :=
    ForcingAssignedParameterConstruction.construct hM hOrder hChoice localEnv (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up zero) 0 1 (up high) 2 3 4 7 (up Q) (up values) (up groundTop) (up seedMul) (up seedUnit) (up seedMark) (up seedH) (up seedC) (up ordinalOne) (up u) (up seedK) (up stageBound) (up P) (up outerF) 8 10 11
    hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE
    hVertices hDiagrams hObj hctx hrec hindex hf hHigh hBits hCoords hSpace hChains hReps.1.1
  exact ⟨vertices,names,diagrams,objImage,objects,arrows,mapImage,maps,orbitQuotient,pr,reps,chains,records,Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hDiagrams,hObj,hObjects,hArrows,hMaps,hMapFamily,hSystem,hCommon,hVertices,hNames,hpr,hQuotient,hProjection,hReps,hChains,hRecords,hProjections,hGerms⟩

def parents {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero high : Fin k)
    (base : Fin k → Fin n) (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin n) : Project.Formula 1 n :=
  let localMap := frame base vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains
  (.conj (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (base (rho 0)) (base I) diagrams))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.conj (ForcingLabelSystem.objectFamily (base (rho 0)) diagrams objects)
    (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (base (rho 0)) (base mul) diagrams arrows))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.conj (ForcingLabelSystem.mapFamily objects arrows maps)
    (.conj (ForcingEligibleSystem.system (base (rho 0)) objects maps)
    (.conj (ForcingConcreteLabels.commonFibers (base (rho 0)) (base I) (base mul) objects maps)
    (.conj (ConstructionComponentCarrier.carrier (base (rho 0)) (base I) (base mul) (base q) vertices)
    (.conj (.forallE (.iff (.mem (.bound 0) (.bound names.succ)) (ProjectSyntax.encode id (ForcingPowerName.candidate (fun j => (base (rho j)).succ) (base G).succ (base F).succ (base bound).succ 0))))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr vertices orbitQuotient))
    (.conj (ForcingOrbitQuotient.classes (base (rho 0)) (base I) (base mul) (base q) vertices orbitQuotient)
    (.conj (ForcingOrbitQuotient.projection (base (rho 0)) (base I) (base mul) (base q) vertices pr)
    (.conj (ConstructionGermDetectors.representatives vertices orbitQuotient reps)
    (.conj (ForcingOrbitChains.family (base w) (base (rho 0)) (base I) (base mul) (base q) (base zero) vertices orbitQuotient reps chains)
    (.conj (ForcingOrbitParameterFamily.family (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up zero) 1 (up high) 4 7 10 11 8 localMap records)
    (.conj (ForcingAssignedParameters.projections (base high) orbitQuotient records reps chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders)
    (ForcingAssigned.germs (base (rho 0)) (base I) (base mul) (base q) reps Germs))))))))))))))))))


theorem parents_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero high : Fin k)
    (base : Fin k → Fin n) (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin n) :
    (parents rho I K B w G F mul q bound labels E zero high base vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders).FreeClosed := by
  simp -implicitDefEqProofs [parents,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCarrier.carrier_freeClosed,
    ForcingLabelSystem.objectFamily_freeClosed,
    ForcingLabelSystem.mapFamily_freeClosed,
    ForcingConcreteLabels.commonFibers_freeClosed,ForcingEligibleSystem.system_freeClosed,
    ForcingOrbitQuotient.classes_freeClosed,
    ForcingOrbitQuotient.projection_freeClosed,
    ConstructionGermDetectors.representatives_freeClosed,
    ForcingOrbitChains.family_freeClosed,
    ForcingOrbitParameterFamily.family_freeClosed,
    ForcingAssignedParameters.projections_freeClosed,
    ForcingAssigned.germs_freeClosed]

theorem parents_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k)
    (I K B w G F mul q bound labels E zero high : Fin k) (base : Fin k → Fin n) (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin n) :
    Project.Formula.satisfies env (parents rho I K B w G F mul q bound labels E zero high base vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) ↔
      Parents hM (fun j => env.bound (base j)) rho I K B w G F mul q bound labels E zero high
        (env.bound vertices) (env.bound names) (env.bound diagrams) (env.bound objImage) (env.bound objects) (env.bound arrows) (env.bound mapImage) (env.bound maps) (env.bound orbitQuotient) (env.bound pr) (env.bound reps) (env.bound chains) (env.bound records) (env.bound Codes) (env.bound Orders) (env.bound Ranks) (env.bound Selections) (env.bound Bounds) (env.bound Labels) (env.bound Tables) (env.bound Diagrams) (env.bound Germs) (env.bound Quotients) (env.bound Nonidentities) (env.bound Highs) (env.bound Detectors) (env.bound PatternOrders) := by
  have hMap {a b : Nat} (v : Fin b → M.Carrier .set) (g : Fin a → Fin b) (vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains : Fin b) :
      (fun j => v (frame g vertices names diagrams objImage objects arrows mapImage maps orbitQuotient pr reps chains j)) =
      frame (fun j => v (g j)) (v vertices) (v names) (v diagrams) (v objImage) (v objects) (v arrows) (v mapImage) (v maps) (v orbitQuotient) (v pr) (v reps) (v chains) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j
          · rfl
          · refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · refine Fin.cases ?_ (fun j => ?_) j
              · rfl
              · refine Fin.cases ?_ (fun j => ?_) j
                · rfl
                · refine Fin.cases ?_ (fun j => ?_) j
                  · rfl
                  · refine Fin.cases ?_ (fun j => ?_) j
                    · rfl
                    · refine Fin.cases ?_ (fun j => ?_) j
                      · rfl
                      · refine Fin.cases ?_ (fun j => ?_) j
                        · rfl
                        · refine Fin.cases ?_ (fun j => ?_) j
                          · rfl
                          · rfl
  simp only [parents,Parents,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,
    ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,
    ForcingEligibleSystem.system_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,
    ForcingPowerName.candidate_semantics (M := M),
    ForcingOrbitQuotient.classes_semantics hM,
    ForcingOrbitQuotient.projection_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,
    ForcingOrbitChains.family_semantics hM,
    ForcingOrbitParameterFamily.family_semantics hM,
    ForcingAssignedParameters.projections_semantics hM,
    ForcingAssigned.germs_semantics hM,hMap]
  rfl

def premises {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k) : List (Project.Formula 1 k) :=
  [ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one),
   ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul,
   ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
   Project.Formula.isOmega (.bound w),
   Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
   ConstructionSaturationIndex.hartogs mu I,
   ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu),
   ProjectSyntax.encode id (ForcingSupportSize.small w mu),
   ConstructionSaturationMergers.allMergers w history K,
   ConstructionTowerHistory.row history K (rho 0) mul one mark H C incoming base K,
   ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels),
   ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound),
   ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound),
   ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I),
   ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A),
   ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq),
   ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E),
   ConstructionSaturationIterationCases.context w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne u seedK mu stageBound,
   ConstructionSaturationIteration.recursive w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne seedK mu stageBound stageBound history,
   ConstructionSaturationIndex.data w mu K stageBound,
   ConstructionTowerTransitions.matrix stageBound history zero P outerF,
   Project.Formula.isSuccessor (.bound high) (.bound zero),
   Project.Formula.isSuccessor (.bound B) (.bound high),
   ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K (rho 1)),
   ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 1) B (rho 2)),
   ConstructionRoundStepSyntax.objectFields w Q values groundTop (rho 0) mul one mark H C]

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k) : Project.Sentence where
  formula :=
    let lift : Fin k → Fin (k+27) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Project.Formula.forallClosure k ((premises rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF).foldr (fun a b => .imp a b)
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (parents rho I K B w G F mul q bound labels E zero high lift 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [premises,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,

      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      Project.Formula.isSuccessor,
      parents_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed]


theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  change Project.Formula.satisfies { bound := env, free := free }
    ((premises rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF).foldr (fun a b => .imp a b) _)
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
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
    parents_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,

    ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    Project.Formula.satisfies_isSuccessor_iff,ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construct hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF


theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)).mp
      (construction_models rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ForcingAssignedParentSystem
