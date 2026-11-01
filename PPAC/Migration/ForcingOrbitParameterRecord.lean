/- Fixed OrbitAssignments.orbitChain/Assigned and ConcreteQuotients.component_selector_dense.
One internal record retains the SAME root, chain, code ranks, actual label fiber,
ordinal table and selector witnesses. Reuses three existing nine-field packs and
one existing triple code; no new codec, choice backend or proof kernel. -/
import PPAC.Migration.ForcingOrbitCodeParameters
import PPAC.Migration.ConstructionSelectorPresentation
import PPAC.Migration.ForcingComponentFibers

namespace PPAC.Migration.ForcingOrbitParameterRecord
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Record (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k)
    (output : M.Carrier .set) : Prop :=
  let up : Fin k → Fin (k+4) := fun j => j.succ.succ.succ.succ
  ∃ r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC,
    ConstructionRoundSelection.Pack (env root) (env chain) r index U labelSet codes order group packA ∧
    ConstructionRoundSelection.Pack support fixing ranks selection rankBound tab germGroup quotient projection packB ∧
    ConstructionRoundSelection.Pack reps N X detector J patternCarrier patternOrder selectorDomain selector packC ∧
    ConstructionComponentCarrier.Code output packA packB packC ∧
    ConstructionComponentCarrier.Code (env root) r index U ∧
    ForcingComponentFibers.VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) labelSet ∧
    ForcingOrbitCodeParameters.Data hM (Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r env)))) (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up names) 3 0 codes order group support fixing ranks selection rankBound tab ∧
    ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) germGroup quotient projection reps N X detector J (env high) (env B) (env (rho 1)) (env (rho 2)) patternCarrier patternOrder selectorDomain selector

def record {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k)
    (base : Fin k → Fin n) (output : Fin n) : Project.Formula 1 n :=
  let lift : Fin k → Fin (k+4) := fun j => j.succ.succ.succ.succ
  let up : Fin n → Fin (n+28) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let localMap : Fin (k+4) → Fin (n+28) := Fin.cases 24 (Fin.cases 25 (Fin.cases 26 (Fin.cases 27 (fun j => up (base j)))))
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (ConstructionRoundSelection.pack (up (base root)) (up (base chain)) 27 26 25 24 23 22 21 2)
    (.conj (ConstructionRoundSelection.pack 20 19 18 17 16 15 14 13 12 1)
    (.conj (ConstructionRoundSelection.pack 11 10 9 8 7 6 5 4 3 0)
    (.conj (ConstructionComponentCarrier.code (up output) 2 1 0)
    (.conj (ConstructionComponentCarrier.code (up (base root)) 27 26 25)
    (.conj (ForcingComponentFibers.vertexFiber (up (base (rho 0))) (up (base mul)) (up (base objects)) (up (base maps)) (up (base root)) 24)
    (.conj (ForcingOrbitCodeParameters.data (fun j => lift (rho j)) (lift I) (lift G) (lift F) (lift mul) (lift q) (lift bound) (lift labels) (lift E) (lift root) (lift w) (lift chain) (lift names) 3 0 localMap 23 22 21 20 19 18 17 16 15)
    (ConstructionConcreteSelector.resultFormula (up (base w)) (up (base (rho 0))) (up (base I)) (up (base mul)) (up (base q)) (up (base root)) (up (base chain)) (up (base K)) (up (base zero)) 14 13 12 11 10 9 8 7 (up (base high)) (up (base B)) (up (base (rho 1))) (up (base (rho 2))) 6 5 4 3))))))))))))))))))))))))))))))))))))

theorem record_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k)
    (base : Fin k → Fin n) (output : Fin n) :
    (record rho I K B w G F mul q bound labels E zero root chain names high objects maps base output).FreeClosed := by
  simp -implicitDefEqProofs [record,Definitional.Formula.FreeClosed,
    ConstructionRoundSelection.pack_freeClosed,ConstructionComponentCarrier.code_freeClosed,
    ForcingComponentFibers.vertexFiber_freeClosed,ForcingOrbitCodeParameters.data_freeClosed,
    ConstructionConcreteSelector.resultFormula_freeClosed]

theorem record_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k)
    (I K B w G F mul q bound labels E zero root chain names high objects maps : Fin k) (base : Fin k → Fin n) (output : Fin n) :
    Project.Formula.satisfies env (record rho I K B w G F mul q bound labels E zero root chain names high objects maps base output) ↔
      Record hM (fun j => env.bound (base j)) rho I K B w G F mul q bound labels E zero root chain names high objects maps (env.bound output) := by
  have hMap {m : Nat} (v : Fin m → M.Carrier .set) (g : Fin k → Fin m) (a b c d : Fin m) :
      (fun j : Fin (k+4) => v (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d g))) j)) =
      Fin.cases (v a) (Fin.cases (v b) (Fin.cases (v c) (Fin.cases (v d) (fun j => v (g j))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  simp only [record,Record,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionRoundSelection.pack_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingComponentFibers.vertexFiber_semantics hM,ForcingOrbitCodeParameters.data_semantics hM,
    ConstructionConcreteSelector.resultFormula_semantics hM,hMap]
  rfl

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k)
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
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
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
    (hSpace : ForcingCohenCoordinates.Cartesian (env (rho 1)) (env B) (env (rho 2))) :
    ∃ output, Record hM env rho I K B w G F mul q bound labels E zero root chain names high objects maps output := by
  have hRoot := (hVertices (env root)).mp (hChain.1.2 (env zero) (env root) hChain.2.1)
  obtain ⟨labelSet,hFiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj hRoot
  obtain ⟨r,index,U,hRootCode,_⟩ := hRoot
  let other : Fin (k+4) → M.Carrier .set := Fin.cases labelSet (Fin.cases U (Fin.cases index (Fin.cases r env)))
  let up : Fin k → Fin (k+4) := fun j => j.succ.succ.succ.succ
  obtain ⟨codes,order,group,support,fixing,ranks,selection,rankBound,tab,hData⟩ :=
    ForcingOrbitCodeParameters.construct hM hChoice other (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up K) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up zero) (up root) (up vertices) (up chain) (up names) 3 2 1 0
      hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hRootCode
  obtain ⟨germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,hSelector⟩ :=
    ConstructionSelectorPresentation.construction_in_presentation hM hOrder hChoice
      hctx hrec hindex hf hRow hVertices hChain hq hHigh hBits hCoords hSpace
  obtain ⟨packA,hpackA⟩ := ConstructionRoundSelection.pack_exists hM (env root) (env chain) r index U labelSet codes order group
  obtain ⟨packB,hpackB⟩ := ConstructionRoundSelection.pack_exists hM support fixing ranks selection rankBound tab germGroup quotient projection
  obtain ⟨packC,hpackC⟩ := ConstructionRoundSelection.pack_exists hM reps N X detector J patternCarrier patternOrder selectorDomain selector
  obtain ⟨output,hOutput⟩ := ConstructionComponentCarrier.code_total hM packA packB packC
  exact ⟨output,r,index,U,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hpackA,hpackB,hpackC,hOutput,hRootCode,hFiber,hData,hSelector⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
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
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
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
    (.existsE (record rho I K B w G F mul q bound labels E zero root chain names high objects maps Fin.succ 0)))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,
      Project.Formula.isSuccessor,record_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)).TrueIn M := by
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
    ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,record_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,
    Project.Formula.satisfies_isSuccessor_iff,ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construct hM hOrder hChoice env rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF)).mp
      (construction_models rho I K B w G F mul one mu history mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names high diagrams objImage objects maps Q values groundTop seedMul seedUnit seedMark seedH seedC ordinalOne u seedK stageBound P outerF hL (ConstructionRoundSelection.l_order hM) hChoice)


end PPAC.Migration.ForcingOrbitParameterRecord
