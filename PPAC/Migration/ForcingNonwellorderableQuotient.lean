/- Pinned ConcreteQuotients.nonwellorderable_quotient_bijection:401-443.
Consume the actual outside-class witness, the SAME newly extended root's actual
common parents, and the existing concrete quotient-bijection proof.
No supplied assignment/record family or assumed final bijection. -/
import PPAC.Migration.ForcingAssignedParentSystem
import PPAC.Migration.ForcingOutsideClassSet
import PPAC.Migration.ForcingConcreteQuotientBijection

namespace PPAC.Migration.ForcingNonwellorderableQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingMapConditions (MapRel)
open ForcingProductFamily (actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingSupportSize (Injection Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem data_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain names r labelSet : Fin k) (codes order group support fixing ranks selection rankBound tab : M.Carrier .set) :
    ForcingOrbitCodeParameters.Data hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base root) (base w) (base chain) (base names) (base r) (base labelSet) codes order group support fixing ranks selection rankBound tab ↔
      ForcingOrbitCodeParameters.Data hM env rho I G F mul q bound labels E root w chain names r labelSet codes order group support fixing ranks selection rankBound tab := by
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  let otherUp : Fin n → Fin (n+2) := fun j => j.succ.succ
  let oldEnv : Fin (k+2) → M.Carrier .set := Fin.cases order (Fin.cases codes env)
  let newEnv : Fin (n+2) → M.Carrier .set := Fin.cases order (Fin.cases codes other)
  let lift : Fin (k+2) → Fin (n+2) := Fin.cases 0 (Fin.cases 1 (fun j => otherUp (base j)))
  have hLift (i : Fin (k+2)) : newEnv (lift i) = oldEnv i :=
    Fin.cases rfl (Fin.cases rfl (fun j => he j)) i
  have hSelected (a d : M.Carrier .set) :
      ForcingCodeSelection.IsSelected newEnv (fun j => otherUp (base (rho j))) (otherUp (base I)) (otherUp (base G)) (otherUp (base F)) (otherUp (base mul)) (otherUp (base q)) (otherUp (base bound)) (otherUp (base labels)) (otherUp (base E)) (otherUp (base root)) (otherUp (base w)) (otherUp (base chain)) 1 0 a d ↔
      ForcingCodeSelection.IsSelected oldEnv (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 1 0 a d :=
    ForcingCodeRanks.selected_reindex oldEnv newEnv lift hLift (fun j => up (rho j))
      (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 1 0 a d
  dsimp only [oldEnv,newEnv,up,otherUp] at hSelected
  simp only [ForcingOrbitCodeParameters.Data,ForcingCohenSelection.Covariant,
    ForcingCohenRankConsumers.Monotone,ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,
    ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
    ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,ForcingCodeSelection.mapRel_relation hM,
    id_eq,hSelected,Fin.cases_succ,he]


private theorem record_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k) (output : M.Carrier .set) :
    ForcingOrbitParameterRecord.Record hM other (fun j => base (rho j)) (base I) (base K) (base B) (base w) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base zero) (base root) (base chain) (base names) (base high) (base objects) (base maps) output ↔
      ForcingOrbitParameterRecord.Record hM env rho I K B w G F mul q bound labels E zero root chain names high objects maps output := by
  have hData (r index U labelSet codes order group support fixing ranks selection rankBound tab : M.Carrier .set) :
      ForcingOrbitCodeParameters.Data hM (Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r other))))
        (fun j => (base (rho j)).succ.succ.succ.succ) (base I).succ.succ.succ.succ (base G).succ.succ.succ.succ (base F).succ.succ.succ.succ (base mul).succ.succ.succ.succ (base q).succ.succ.succ.succ (base bound).succ.succ.succ.succ (base labels).succ.succ.succ.succ (base E).succ.succ.succ.succ (base root).succ.succ.succ.succ (base w).succ.succ.succ.succ (base chain).succ.succ.succ.succ (base names).succ.succ.succ.succ 3 0 codes order group support fixing ranks selection rankBound tab ↔
      ForcingOrbitCodeParameters.Data hM (Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r env))))
        (fun j => (rho j).succ.succ.succ.succ) I.succ.succ.succ.succ G.succ.succ.succ.succ F.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ bound.succ.succ.succ.succ labels.succ.succ.succ.succ E.succ.succ.succ.succ root.succ.succ.succ.succ w.succ.succ.succ.succ chain.succ.succ.succ.succ names.succ.succ.succ.succ 3 0 codes order group support fixing ranks selection rankBound tab :=
    data_reindex hM
      (Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r env))))
      (Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r other))))
      (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (fun j => (base j).succ.succ.succ.succ)))))
      (fun j => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => he i)))) j)
      (fun j => (rho j).succ.succ.succ.succ) I.succ.succ.succ.succ G.succ.succ.succ.succ F.succ.succ.succ.succ
      mul.succ.succ.succ.succ q.succ.succ.succ.succ bound.succ.succ.succ.succ labels.succ.succ.succ.succ E.succ.succ.succ.succ
      root.succ.succ.succ.succ w.succ.succ.succ.succ chain.succ.succ.succ.succ names.succ.succ.succ.succ 3 0
      codes order group support fixing ranks selection rankBound tab
  simp only [ForcingOrbitParameterRecord.Record,he,hData]

private theorem family_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient : Fin k) (records : M.Carrier .set) :
    ForcingOrbitParameterFamily.Family hM other (fun j => base (rho j)) (base I) (base K) (base B) (base w) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base zero) (base names) (base high) (base objects) (base maps) (base reps) (base chains) (base orbitQuotient) records ↔
      ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records := by
  have hRecord (root chain : M.Carrier .set) (output : M.Carrier .set) :
      ForcingOrbitParameterRecord.Record hM (Fin.cases chain (Fin.cases root other))
        (fun j => (base (rho j)).succ.succ) (base I).succ.succ (base K).succ.succ (base B).succ.succ (base w).succ.succ (base G).succ.succ (base F).succ.succ (base mul).succ.succ (base q).succ.succ (base bound).succ.succ (base labels).succ.succ (base E).succ.succ (base zero).succ.succ 1 0 (base names).succ.succ (base high).succ.succ (base objects).succ.succ (base maps).succ.succ output ↔
      ForcingOrbitParameterRecord.Record hM (Fin.cases chain (Fin.cases root env))
        (fun j => (rho j).succ.succ) I.succ.succ K.succ.succ B.succ.succ w.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ zero.succ.succ 1 0 names.succ.succ high.succ.succ objects.succ.succ maps.succ.succ output :=
    record_reindex hM (Fin.cases chain (Fin.cases root env)) (Fin.cases chain (Fin.cases root other))
      (Fin.cases 0 (Fin.cases 1 (fun j => (base j).succ.succ)))
      (fun j => Fin.cases rfl (Fin.cases rfl (fun i => he i)) j)
      (fun j => (rho j).succ.succ) I.succ.succ K.succ.succ B.succ.succ w.succ.succ G.succ.succ F.succ.succ
      mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ zero.succ.succ 1 0 names.succ.succ high.succ.succ
      objects.succ.succ maps.succ.succ output
  simp only [ForcingOrbitParameterFamily.Family,ForcingOrbitParameterFamily.At,he,hRecord]

private theorem value_congr {k n : Nat} {R : Source.Formula (k+2)} {S : Source.Formula (n+2)}
    {H : Source.Formula (k+1)} {J : Source.Formula (n+1)}
    {env : Fin k → M.Carrier .set} {other : Fin n → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, ForcingClassEvaluation.Predicate H env x ↔ ForcingClassEvaluation.Predicate J other x)
    (v : Fin 7 → M.Carrier .set) (G F I K c t b labels E i name : M.Carrier .set) :
    ForcingRelationClassMove.Value R H env v G F I K c t b labels E i name ↔
      ForcingRelationClassMove.Value S J other v G F I K c t b labels E i name := by
  simp only [ForcingRelationClassMove.Value,ForcingRelationClass.Class,ForcingSeparation.Separated,
    ForcingSeparation.atomic_congr hR,ForcingSeparation.force_congr hR hH]

private theorem quotient_reindex {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) (name : M.Carrier .set) :
    ForcingQuotientName.Quotient other (fun j => base (rho j)) (base G) (base F) (base mul) (base I)
      (base K) (base c) (base t) (base b) (base labels) (base E) name ↔
      ForcingQuotientName.Quotient env rho G F mul I K c t b labels E name := by
  have hR (x y : M.Carrier .set) :
      MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔ MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  have hH (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,he]
  simp only [ForcingQuotientName.Quotient,ForcingQuotientName.Family,
    ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
    ForcingRelationClassMove.family_semantics,value_congr hR hH,he]
  rfl

private theorem above (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF d0 name z0 groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env K))
    (hRow : ConstructionTowerHistory.Row (env history) (env K) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env K))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hObjFields : ConstructionRoundFields.ObjectFields hM (env w) (env Q) (env values) (env groundTop) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d0))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d0) (env q))
    (hEHS : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name))
    (hUncountable : ¬ ForcingSupportSize.Small (env K) (env w))
    (hCoding : Injection (env K) (env groundValues) (env labelMap))
    (hLo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hBit : (Project.FirstOrderSemantics.reduct M).mem (env bit) (env B))
    (hBitSuccessor : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) (env high))
    (hBits : env lo ≠ env bit)
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hSubq : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hKLeMu : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env K))
    (hbNe : env b ≠ env one)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hp) (env E))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : ConstructionCohenCompatibility.Restricted (env Ap) (env d) (env d0))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env s))
    (hj : ConstructionPlacementTriple.ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : ForcingRelationClassMove.Value (orderFormula (rho 0) mul) (domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hctx : ConstructionSaturationIterationCases.Context hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env u) (env seedK) (env mu) (env stageBound))
    (hrec : ConstructionSaturationIteration.Recursive hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env seedK) (env mu) (env stageBound) (env stageBound) (env history))
    (hindex : ConstructionSaturationIndex.Data hM (env w) (env mu) (env K) (env stageBound))
    (hf : ConstructionTowerTransitions.Matrix (env stageBound) (env history) (env zero) (env P) (env outerF))
    (hHigh : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env high) (env zero))
    (hCoords : ForcingCohenCoordinates.Cartesian (env I) (env K) (env (rho 1)))
    (hSpace : ForcingCohenCoordinates.Cartesian (env (rho 1)) (env B) (env (rho 2))) :
    ∃ graph, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) graph ∧
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 graph (env labels) (env name)) (env (rho 6)) (env z0)
        ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) := by
  have hSmall : Small (env w) (env mu) := (ForcingSupportSize.native_small hM _ _).mpr hMu.2
  obtain ⟨vertices,names,diagrams,objImage,objects,arrows,mapImage,maps,orbitQuotient,pr,reps,chains,records,Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hParents⟩ :=
    ForcingAssignedParentSystem.construct hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF
    hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hctx hrec hindex hf hHigh hBitSuccessor hCoords hSpace hObjFields
  obtain ⟨hDiagrams,hObj,hObjects,hArrows,hMaps,hMapFamily,_,hCommon,hVertices,hNames,_,hQuotient,hProjection,hReps,hChains,hRecords,hProjections,_⟩ := hParents
  let oldEnv : Fin (k+12) → M.Carrier .set := Fin.cases vertices (Fin.cases names (Fin.cases diagrams (Fin.cases objImage (Fin.cases objects (Fin.cases arrows (Fin.cases mapImage (Fin.cases maps (Fin.cases orbitQuotient (Fin.cases pr (Fin.cases reps (Fin.cases chains (env))))))))))))
  let upOld : Fin k → Fin (k+12) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let full : Fin (k+27) → M.Carrier .set := Fin.cases records (Fin.cases Codes (Fin.cases Orders (Fin.cases Ranks (Fin.cases Selections (Fin.cases Bounds (Fin.cases Labels (Fin.cases Tables (Fin.cases Diagrams (Fin.cases Germs (Fin.cases Quotients (Fin.cases Nonidentities (Fin.cases Highs (Fin.cases Detectors (Fin.cases PatternOrders (oldEnv)))))))))))))))
  let lift : Fin (k+12) → Fin (k+27) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let up : Fin k → Fin (k+27) := fun j => lift (upOld j)
  have he (i : Fin k) : full (up i) = env i := rfl
  have hRecordFull := (family_reindex hM oldEnv full lift (fun _ => rfl)
    (fun j => upOld (rho j)) (upOld I) (upOld K) (upOld B) (upOld w) (upOld G) (upOld F) (upOld mul) (upOld q) (upOld bound) (upOld labels) (upOld E) (upOld zero) 1 (upOld high) 4 7 10 11 8 records).mpr hRecords
  let families : Fin 16 → Fin (k+27) := Fin.cases 25 (Fin.cases 26 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 5 (Fin.cases 6 (Fin.cases 7 (Fin.cases 8 (Fin.cases 9 (Fin.cases 10 (Fin.cases 11 (Fin.cases 12 (Fin.cases 13 (fun _ => 14)))))))))))))))
  have hQ := hctx.2.1
  have hR := hctx.2.2.1
  have huQ := (hQ (env u)).mpr ⟨env ordinalOne,env ordinalOne,hctx.2.2.2.1⟩
  have hTopCut := ConstructionRealCuts.principal_cut hM hw hQ huQ hctx.2.2.2.2.2.1
  have hOrderRel (x y : M.Carrier .set) :
      MapRel (orderFormula (up (rho 0)) (up mul)) full x y ↔ MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  have hDomain (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => up (rho j)) (up G) (up F)) full x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,he]
  have hNameFull := (quotient_reindex env full up he rho G F mul I K labelMap top bit labels E (env name)).mpr hName
  have hSigmaFull := (value_congr hOrderRel hDomain (fun j => env (rho j)) (env G) (env F) (env I) (env K)
    (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma)).mpr hSigma
  have hOutsideFull : ForcingOutsideLocal.Outside (orderFormula (up (rho 0)) (up mul)) full
      (env (rho 6)) (env z) (env sigma) (env list) := by
    intro r hr hrz hmem
    exact hOut r hr ((hOrderRel r (env z)).mp hrz)
      ((ForcingSeparation.atomic_congr hOrderRel false _ _ _ _).mp hmem)
  obtain ⟨graph,_,hHS,hSupp,hForce⟩ := ForcingConcreteQuotientBijection.quotient_bijection_above hM hChoice full (fun j => up (rho j))
    (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up K) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up zero) 15 16 17 18 19 22 23 24 20 21 (up high) 0 (up d0) (up name) (up z0) (up Q) (up values) (up groundTop) (up groundValues) (up lo) (up p) (up b) (up Ap) (up Hp) (up XP) (up ordinal) (up enum) (up list) (up Power) (up continuum) (up s) (up j) (up sigma) (up d) (up z) families
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hctx.2.2.2.2.2.2.2.1 hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecordFull hProjections hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hNameFull hUncountable hCoding hLo hBit hBits hpI hSubq hAp hHp hXP hb hEnum hList hTwo hKLeMu hParameters hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hSigmaFull hOutsideFull
  exact ⟨graph,hHS,hSupp,(ForcingSeparation.force_congr hOrderRel hDomain _ _ _ _).mp hForce⟩

theorem nonwellorderable (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial : Fin k)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env K))
    (hRow : ConstructionTowerHistory.Row (env history) (env K) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env K))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hObjFields : ConstructionRoundFields.ObjectFields hM (env w) (env Q) (env values) (env groundTop) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hEHS : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name))
    (hUncountable : ¬ ForcingSupportSize.Small (env K) (env w))
    (hCoding : Injection (env K) (env groundValues) (env labelMap))
    (hLo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hBit : (Project.FirstOrderSemantics.reduct M).mem (env bit) (env B))
    (hBitSuccessor : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) (env high))
    (hBits : env lo ≠ env bit)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hKLeMu : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env K))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hctx : ConstructionSaturationIterationCases.Context hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env u) (env seedK) (env mu) (env stageBound))
    (hrec : ConstructionSaturationIteration.Recursive hM (env w) (env Q) (env values) (env groundTop) (env w) (env seedMul) (env seedUnit) (env seedMark) (env seedH) (env seedC) (env zero) (env ordinalOne) (env seedK) (env mu) (env stageBound) (env stageBound) (env history))
    (hindex : ConstructionSaturationIndex.Data hM (env w) (env mu) (env K) (env stageBound))
    (hf : ConstructionTowerTransitions.Matrix (env stageBound) (env history) (env zero) (env P) (env outerF))
    (hHigh : (Project.FirstOrderSemantics.reduct M).SuccessorOf (env high) (env zero))
    (hCoords : ForcingCohenCoordinates.Cartesian (env I) (env K) (env (rho 1)))
    (hSpace : ForcingCohenCoordinates.Cartesian (env (rho 1)) (env B) (env (rho 2)))
    (hInitial : (Project.FirstOrderSemantics.reduct M).mem (env initial) (env (rho 6)))
    (hNot : ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
      (Source.SetLanguage.args1 (env name)) (env (rho 6)) (env initial) (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env r (env initial) ∧
      ∃ graph, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
        ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
          (Source.SetLanguage.args3 graph (env labels) (env name)) (env (rho 6)) r
          ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hSmallW : Small (env w) (env mu) := (ForcingSupportSize.native_small hM _ _).mpr hMu.2
  have hLarge : ¬ Small (env I) (env mu) := fun h =>
    hI.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  obtain ⟨seed,hSeed⟩ := ConstructionDiagramAmalgamation.whole_embedding hM hMu.1 hI hSmallD
  obtain ⟨d0,root,z0,hd0,hRoot,hz0,hz0Initial⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hSeed hInitial
  have hz0W := ForcingSupportingRoot.code_mem hp hd0 hRoot hz0
  obtain ⟨stabilizer,hStabilizer,hStabilizerF⟩ := ForcingHS.symmetric_of_hs hEHS
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hF stabilizer).mp hStabilizerF
  have hESupport : ForcingSupportedNames.Supported (fun j => env (rho j)) HJ (env E) := by
    intro pi hpi ac hac
    obtain ⟨a,ha,hFixed⟩ := ((hStabilizer pi).mp (hIncluded pi hpi)).2
    have hActionEq := ForcingProductFamily.unique hM
      ((ForcingProductFamily.mapRel_action _ _ _).mp ha) ((ForcingProductFamily.mapRel_action _ _ _).mp hac)
    exact hActionEq ▸ hFixed
  obtain ⟨support,hSupport,hSupportI,hSupportW⟩ := ConstructionCohenCompatibility.exists_support hM hw hp.1 hp.2.1 hd0
  obtain ⟨sm,hsm⟩ := (ForcingSupportSize.native_small hM support (env w)).mp hSupportW
  obtain ⟨wm,hwm⟩ := hMu.2
  have hSupportMu := ZF.exists_compositionInjection hZF pair hsm hwm
  obtain ⟨cover,hUnion⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) J support
  have hCoverI : (Project.FirstOrderSemantics.reduct M).MemberSubset cover (env I) := by
    intro x hx
    exact (hUnion x).mp hx |>.elim (hJI x) (hSupportI x)
  have hCoverMu : Small cover (env mu) := (ForcingSupportSize.native_small hM _ _).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM _ _).mp hJSmall) hSupportMu hUnion)
  obtain ⟨p,hpI,hSubp,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hRoot hCoverI hCoverMu
  obtain ⟨Ap,hAp,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hpI hSmallD
  obtain ⟨Hp,hHp⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Ap
  have hJAp : (Project.FirstOrderSemantics.reduct M).MemberSubset J Ap := fun x hx =>
    (hAp x).mpr (hCover x ((hUnion x).mpr (Or.inl hx)))
  have hEp := ForcingSupportedNames.supported_mono hFixJ hHp hJAp hESupport
  obtain ⟨zp,hzp⟩ := ForcingSupportingRoot.exists_code hM d0 p
  have hzpW := ForcingSupportingRoot.code_mem hp hd0 hpI hzp
  have hzpz0 := (ForcingSupportingRoot.code_le hzp hz0).mpr
    ⟨fun _ hx => hx,env mark,hMark,hSubp⟩
  have hzpInitial := hpre.2 zp z0 (env initial) hzpW hz0W hInitial
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul zp z0).mpr hzpz0)
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul z0 (env initial)).mpr hz0Initial)
  have hnotp := ForcingFormula.mono hM hpre (ForcingCheckOrdinal.wellorderable 0).neg
    (Source.SetLanguage.args1 (env name)) hInitial hzpW hzpInitial hNot
  obtain ⟨XP,ordinal,enum,list,hXP,hOrdinal,hEnum,hList,_⟩ := ForcingLocalList.construct hM hChoice
    (fun j => env (rho j)) hw hMu hp hG hF hpI hSmallD hAp hHp
  obtain ⟨nalpha,hNalpha⟩ := ForcingCheckName.exists_checked hM (env top) ordinal
  have hRawOrdinal : ForcingRawRank.Ordinal ordinal := by
    simp only [ForcingRawRank.Ordinal,OrdinalSyntax.ordinal,OrdinalSyntax.transitiveSet,
      OrdinalSyntax.linear,OrdinalSyntax.irreflexive,OrdinalSyntax.membershipTransitive,
      OrdinalSyntax.comparable,OrdinalSyntax.wellFounded,OrdinalSyntax.minimalExists,
      OrdinalSyntax.setMinimal,RestrictionSyntax.subset,MinimalPredicates.inhabited,
      Source.Formula.Realize,Source.Formula.neg,Fin.lastCases_last,Fin.lastCases_castSucc]
    refine ⟨(fun x y hx hy => hOrdinal.transitive x hx y hy),⟨hOrdinal.wellOrder.linear.irrefl,?_,?_⟩,?_⟩
    · intro x y z hx hy hz hxy
      exact hOrdinal.wellOrder.linear.trans x hx y hy z hz hxy.1 hxy.2
    · intro x y hx hy
      rcases hOrdinal.wellOrder.linear.compare x hx y hy with he | hxy | hyx
      · exact Or.inl (hZF.1.eq_of_same_members x y he)
      · exact Or.inr (Or.inl hxy)
      · exact Or.inr (Or.inr hyx)
    · intro b hb
      obtain ⟨x,hx,hmin⟩ := hOrdinal.wellOrder.least b hb.1 hb.2
      refine ⟨x,hx,?_⟩
      intro y hy hyx
      rcases hmin y hy with he | hxy
      · have hEq := hZF.1.eq_of_same_members x y he
        subst y
        exact hOrdinal.wellOrder.linear.irrefl x (hb.1 x hx) hyx
      · exact hOrdinal.wellOrder.linear.irrefl x (hb.1 x hx)
          (hOrdinal.wellOrder.linear.trans x (hb.1 x hx) y (hb.1 y hy) x (hb.1 x hx) hxy hyx)
  let before : Fin (k+10) → M.Carrier .set := Fin.cases zp (Fin.cases d0 (Fin.cases p (Fin.cases Ap (Fin.cases Hp (Fin.cases XP (Fin.cases ordinal (Fin.cases enum (Fin.cases list (Fin.cases nalpha (env))))))))))
  let liftBefore : Fin k → Fin (k+10) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have heBefore (i : Fin k) : before (liftBefore i) = env i := rfl
  have hRBefore (x y : M.Carrier .set) :
      MapRel (orderFormula (liftBefore (rho 0)) (liftBefore mul)) before x y ↔ MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heBefore]
  have hHBefore (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (domain (fun j => liftBefore (rho j)) (liftBefore G) (liftBefore F)) before x ↔
      ForcingClassEvaluation.Predicate (domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,heBefore]
  have hYBefore := (quotient_reindex env before liftBefore heBefore rho G F mul I K labelMap top bit labels E (env name)).mpr hName
  have hNotBefore := (ForcingSeparation.force_congr hRBefore hHBefore _ _ _ _).mpr hnotp
  obtain ⟨d,hd,hdd0,s,b,As,Hs,z,j,sigma,hs,hb,hbNe,hSub,hAs,hHs,hWithin,hz,hj,hSigma,_,hOutside⟩ :=
    ForcingOutsideClassSet.denseBelow hM hChoice before (fun i => liftBefore (rho i))
      (liftBefore I) (liftBefore K) (liftBefore B) (liftBefore w) (liftBefore G) (liftBefore F) (liftBefore mul)
      (liftBefore one) (liftBefore mu) (liftBefore mark) 2 3 4 (liftBefore labelMap) (liftBefore top) (liftBefore bit)
      (liftBefore labels) (liftBefore E) (liftBefore bound) 5 6 7 8 9 (liftBefore name) 1 0
      hw hMu hI hm hCard hMark hp hG hF hLabelMap hTop hLabels hLabelBound hpI hAp hHp hEp hEHS hXP hRawOrdinal hEnum hList hNalpha hYBefore hd0 hzp hNotBefore
      d0 hd0 (fun _ hx => hx)
  have hSigmaOld := (value_congr hRBefore hHBefore (fun i => env (rho i)) (env G) (env F) (env I) (env K)
    (env labelMap) (env top) (env bit) (env labels) (env E) j sigma).mp
      ((ForcingRelationClassMove.family_semantics before (fun i => liftBefore (rho i))
        (liftBefore G) (liftBefore F) (liftBefore mul) (liftBefore I) (liftBefore K) (liftBefore labelMap)
        (liftBefore top) (liftBefore bit) (liftBefore labels) (liftBefore E) j sigma).mp hSigma)
  have hOutsideOld : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list := by
    intro r hr hrz hmem
    exact hOutside r hr ((hRBefore r z).mpr hrz)
      ((ForcingSeparation.atomic_congr hRBefore false _ _ _ _).mpr hmem)
  have hSupported : ForcingLocalRecordPullback.Supported (env (rho 0)) s d :=
    fun i k b he => (hAs i).mp (hWithin i k b he)
  have hjImage : ConstructionPlacementTriple.ImageAt s (env (rho 0)) j := (hAs j).mp hj
  have hZero := hctx.2.2.2.2.2.2.2.1
  obtain ⟨q,hq,hSubq,_⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hpI
    (J := env zero) (fun x hx => False.elim (hZero x hx)) (ForcingSupportSize.small_empty hM _ hZero)
  obtain ⟨Aq,hAq,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hSmallD
  obtain ⟨Hq,hHq⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Aq
  have hApAq : (Project.FirstOrderSemantics.reduct M).MemberSubset Ap Aq := fun x hx =>
    (hAq x).mpr (ConstructionDescentPlacement.range_antitone ⟨env mark,hMark,hSubq⟩ ((hAp x).mp hx))
  have hEq := ForcingSupportedNames.supported_mono hHp hHq hApAq hEp
  obtain ⟨dR,hdR,hRestricted,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd Ap
  obtain ⟨r,hrCode⟩ := ForcingSupportingRoot.exists_code hM dR q
  have hrW := ForcingSupportingRoot.code_mem hp hdR hq hrCode
  have hd0dR : (Project.FirstOrderSemantics.reduct M).MemberSubset d0 dR := by
    intro z hz
    obtain ⟨a,ha,b,hb,hCode⟩ := (hp.2.1 z).mp (hd0.1 z hz)
    obtain ⟨i,hi,k,hk,hCoord⟩ := (hp.1 a).mp ha
    have hEntry : ConstructionCohenCompatibility.Entry d0 i k b := ⟨a,hCoord,z,hCode,hz⟩
    have hiSupport := (hSupport i).mpr ⟨k,b,hEntry⟩
    have hiAp := (hAp i).mpr (hCover i ((hUnion i).mpr (Or.inr hiSupport)))
    exact (hRestricted z).mpr ⟨hdd0 z hz,i,⟨a,k,b,hCode,hCoord⟩,hiAp⟩
  have hrz0 := (ForcingSupportingRoot.code_le hrCode hz0).mpr
    ⟨hd0dR,ForcingDiagramPoset.le_trans hm ⟨env mark,hMark,hSubq⟩ ⟨env mark,hMark,hSubp⟩⟩
  have hrInitial := hpre.2 r z0 (env initial) hrW hz0W hInitial
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r z0).mpr hrz0)
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul z0 (env initial)).mpr hz0Initial)
  let after : Fin (k+18) → M.Carrier .set := Fin.cases q (Fin.cases Aq (Fin.cases Hq (Fin.cases dR (Fin.cases r (Fin.cases p (Fin.cases Ap (Fin.cases Hp (Fin.cases XP (Fin.cases ordinal (Fin.cases enum (Fin.cases list (Fin.cases s (Fin.cases b (Fin.cases d (Fin.cases z (Fin.cases j (Fin.cases sigma (env))))))))))))))))))
  let liftAfter : Fin k → Fin (k+18) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have heAfter (i : Fin k) : after (liftAfter i) = env i := rfl
  have hRAfter (x y : M.Carrier .set) :
      MapRel (orderFormula (liftAfter (rho 0)) (liftAfter mul)) after x y ↔ MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heAfter]
  have hHAfter (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (domain (fun j => liftAfter (rho j)) (liftAfter G) (liftAfter F)) after x ↔
      ForcingClassEvaluation.Predicate (domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,heAfter]
  have hYAfter := (quotient_reindex env after liftAfter heAfter rho G F mul I K labelMap top bit labels E (env name)).mpr hName
  have hSigmaAfter := (value_congr hRAfter hHAfter (fun i => env (rho i)) (env G) (env F) (env I) (env K)
    (env labelMap) (env top) (env bit) (env labels) (env E) j sigma).mpr hSigmaOld
  have hOutsideAfter : ForcingOutsideLocal.Outside (orderFormula (liftAfter (rho 0)) (liftAfter mul)) after
      (env (rho 6)) z sigma list := by
    intro r hr hrz hmem
    exact hOutsideOld r hr ((hRAfter r z).mp hrz)
      ((ForcingSeparation.atomic_congr hRAfter false _ _ _ _).mp hmem)
  obtain ⟨graph,hGraphHS,_,hBijection⟩ := above hM hOrder hChoice after (fun i => liftAfter (rho i))
    (liftAfter I) (liftAfter K) (liftAfter B) (liftAfter w) (liftAfter G) (liftAfter F) (liftAfter mul) (liftAfter one) (liftAfter mu) (liftAfter history) (liftAfter mark) (liftAfter H) (liftAfter C) (liftAfter incoming) (liftAfter base) 0 1 2 (liftAfter labelMap) (liftAfter top) (liftAfter bit) (liftAfter labels) (liftAfter E) (liftAfter bound) (liftAfter zero) (liftAfter high) (liftAfter Q) (liftAfter values) (liftAfter groundTop) (liftAfter seedMul) (liftAfter seedUnit) (liftAfter seedMark) (liftAfter seedH) (liftAfter seedC) (liftAfter ordinalOne) (liftAfter u) (liftAfter seedK) (liftAfter stageBound) (liftAfter P) (liftAfter outerF) 3 (liftAfter name) 4 (liftAfter groundValues) (liftAfter lo) 5 13 6 7 8 9 10 11 (liftAfter Power) (liftAfter continuum) 12 16 17 14 15
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hAq hHq hEq hObjFields hMark hCard hdR hrCode hEHS hYAfter hUncountable hCoding hLo hBit hBitSuccessor hBits hpI hSubq hAp hHp hXP hb hEnum hList hTwo hKLeMu hParameters hAllIdeals hbNe hEp hs hSub hd hSupported hRestricted hz hjImage hSigmaAfter hOutsideAfter hBound hctx hrec hindex hf hHigh hCoords hSpace
  exact ⟨r,hrW,hrInitial,graph,hGraphHS,(ForcingSeparation.force_congr hRAfter hHAfter _ _ _ _).mp hBijection⟩

def result {k : Nat} (rho : Fin 7 → Fin k) (G F mul labels name initial : Fin k) : Project.Formula 1 k :=
  .existsE (.conj (.mem (.bound 0) (.bound (rho 6).succ))
    (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) Fin.succ 0 initial.succ))
      (.existsE (.conj
        (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (rho j).succ.succ) G.succ.succ (rho 6).succ.succ F.succ.succ 0))
        (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
          (fun j => j.succ.succ) (Source.SetLanguage.args3 0 labels.succ.succ name.succ.succ) (rho 6).succ.succ 1
          ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))))))))

theorem result_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (G F mul labels name initial : Fin k) :
    (result rho G F mul labels name initial).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

def premises {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial : Fin k) : List (Project.Formula 1 k) :=
  [Project.Formula.isOrdinal (.bound K),
   ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one),
   ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul,
   ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
   Project.Formula.isOmega (.bound w),
   Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
   ConstructionSaturationIndex.hartogs mu I,
   ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu),
   ConstructionSaturationMergers.allMergers w history K,
   ConstructionTowerHistory.row history K (rho 0) mul one mark H C incoming base K,
   ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels),
   ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound),
   ConstructionRoundStepSyntax.objectFields w Q values groundTop (rho 0) mul one mark H C,
   .mem (.bound mark) (.bound (rho 0)),
   ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu,
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E),
   ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id name),
   .neg (ProjectSyntax.encode id (ForcingSupportSize.small K w)),
   ProjectSyntax.encode id (Source.SetLanguage.injection labelMap K groundValues),
   .mem (.bound lo) (.bound B),
   .mem (.bound bit) (.bound B),
   Project.Formula.isSuccessor (.bound B) (.bound high),
   .neg (Project.Formula.extensionalEq (.bound lo) (.bound bit)),
   ForcingProductParameters.two B,
   Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu),
   ConstructionConcreteCardinals.parameters w Power continuum mu,
   ConstructionIdealProbes.allIdeals mu history K,
   ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound),
   ConstructionSaturationIterationCases.context w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne u seedK mu stageBound,
   ConstructionSaturationIteration.recursive w Q values groundTop w seedMul seedUnit seedMark seedH seedC zero ordinalOne seedK mu stageBound stageBound history,
   ConstructionSaturationIndex.data w mu K stageBound,
   ConstructionTowerTransitions.matrix stageBound history zero P outerF,
   Project.Formula.isSuccessor (.bound high) (.bound zero),
   ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K (rho 1)),
   ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 1) B (rho 2)),
   .mem (.bound initial) (.bound (rho 6)),
   ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (Source.SetLanguage.args1 name) (rho 6) initial (ForcingCheckOrdinal.wellorderable 0).neg)]

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k ((premises rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial).foldr
    (fun a b => .imp a b) (result rho G F mul labels name initial))
  freeClosed := by
    simp -implicitDefEqProofs [premises,List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,Project.Formula.extensionalEq,
      ForcingProductParameters.two_freeClosed,ConstructionConcreteCardinals.parameters_freeClosed,
      ConstructionIdealProbes.allIdeals_freeClosed,ConstructionSaturationIterationCases.context_freeClosed,
      ConstructionSaturationIteration.recursive_freeClosed,ConstructionSaturationIndex.data_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,Project.Formula.isSuccessor,result_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  change Project.Formula.satisfies {bound := env,free := free}
    ((premises rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial).foldr (fun a b => .imp a b) _)
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,
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
    ForcingHS.hs_semantics (M := M),
    ForcingQuotientName.quotient_semantics (M := M),
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
    ForcingFormula.formula_semantics (M := M),id_eq]
  intro hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hObjFields hMark hCard hEHS hName hUncountable hCoding hLo hBit hBitSuccessor hBits hTwo hKLeMu hParameters hAllIdeals hBound hctx hrec hindex hf hHigh hCoords hSpace hInitial hNot
  obtain ⟨r,hr,hrInitial,graph,hHS,hForce⟩ := nonwellorderable hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hObjFields hMark hCard hEHS hName hUncountable hCoding hLo hBit hBitSuccessor hBits hTwo hKLeMu hParameters hAllIdeals hBound hctx hrec hindex hf hHigh hCoords hSpace hInitial hNot
  simp only [result,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingFormula.formula_semantics (M := M)]
  refine ⟨r,hr,hrInitial,graph,hHS,?_⟩
  have hargs : (fun i => (Fin.cases graph (Fin.cases r env) : Fin (k+2) → M.Carrier .set)
      (Source.SetLanguage.args3 0 labels.succ.succ name.succ.succ i)) =
      Source.SetLanguage.args3 graph (env labels) (env name) := by
    funext i
    exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.elim0 i) i) i) i
  change ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
    (fun i => (Fin.cases graph (Fin.cases r env) : Fin (k+2) → M.Carrier .set)
      (Source.SetLanguage.args3 0 labels.succ.succ name.succ.succ i))
    (env (rho 6)) r ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))
  rw [hargs]
  exact hForce

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial))) := by
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
  apply ConstructibleGround.relative_models hM (sentence rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial)).mp
      (models rho I K B w G F mul one mu history mark H C incoming base labelMap top bit labels E bound zero high Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF name groundValues lo Power continuum initial hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ForcingNonwellorderableQuotient
