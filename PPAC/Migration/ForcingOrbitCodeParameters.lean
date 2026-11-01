/- Fixed CodeLinks.ordinalRank/ordinalType and GermSelectors.Preliminary data.
Construct the actual code carrier, internal well-order, fixed rank/type witnesses
and rank-bounded ordinal table for the SAME orbit chain from existing producers.
Consumer: the actual auxiliary parameter family of OrbitAssignments.Assigned. -/
import PPAC.Migration.ForcingCodeRanks
import PPAC.Migration.ConstructionGermPatternOrder
import PPAC.Migration.ForcingGermDensity

namespace PPAC.Migration.ForcingOrbitCodeParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Data (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain names r labelSet : Fin k)
    (codes order group support fixing ranks selection rankBound tab : M.Carrier .set) : Prop :=
  let up : Fin k → Fin (k+2) := fun j : Fin k => j.succ.succ
  let R := ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 1 0
  let L := ForcingCohenSelection.liftRelation R id (up (rho 0)) (up I) (up (rho 2)) (up w)
  let other := Fin.cases order (Fin.cases codes env)
  ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) codes ∧
    (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order codes ∧
    ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) group ∧
    ForcingSupportedNames.Range (env (rho 0)) (env r) support ∧
    ForcingLabelPermutations.Fixing (env G) support fixing ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset fixing group ∧
    ForcingConjugationGraph.Subgroup (env I) (env G) group ∧
    (Project.FirstOrderSemantics.reduct M).mem group (env F) ∧
    ForcingCohenSelection.Covariant R other (env (rho 2)) (env w) group codes ∧
    ForcingCohenRankConsumers.Monotone R other (env (rho 2)) (env w) codes ∧
    ForcingOrdinalRanks.Ranks L other codes order (env (rho 6)) ranks ∧
    ForcingCollectedName.Collected L other codes ranks (env (rho 6)) selection ∧
    ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) group codes ranks ∧
    ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) group selection ∧
    ForcingRawRank.Rank selection rankBound ∧
    ForcingOrdinalTable.Table hM (env labelSet) rankBound tab

def data {k n : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain names r labelSet : Fin k)
    (base : Fin k → Fin n) (codes order group support fixing ranks selection rankBound tab : Fin n) : Project.Formula 1 n :=
  let up : Fin k → Fin (k+2) := fun j : Fin k => j.succ.succ
  let R := ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 1 0
  let L := ForcingCohenSelection.liftRelation R id (up (rho 0)) (up I) (up (rho 2)) (up w)
  let localMap : Fin (k+2) → Fin n := Fin.cases order (Fin.cases codes base)
  (.conj (ForcingTailCodes.carrier (fun j => base (rho j)) (base G) (base F) (base bound) (base w) (base names) (base chain) codes)
    (.conj (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.conj (ForcingTailGroup.tailGroup (base w) (base (rho 0)) (base G) (base chain) group)
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (base (rho 0)) (base r) support))
    (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (base G) support fixing))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset fixing group))
    (.conj (ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (base I) (base G) group))
    (.conj (.mem (.bound group) (.bound (base F)))
    (.conj (ForcingCohenSelection.covariant R localMap (base (rho 2)) (base w) group codes)
    (.conj (ProjectSyntax.encode id (ForcingCohenRankConsumers.monotone R localMap (base (rho 2)) (base w) codes))
    (.conj (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L localMap codes order (base (rho 6)) ranks))
    (.conj (ProjectSyntax.encode id (ForcingCollectedName.collected L localMap codes ranks (base (rho 6)) selection))
    (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily (fun j => base (rho j)) (base G) (base F) group codes ranks))
    (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => base (rho j)) (base G) (base F) group selection))
    (.conj (ProjectSyntax.encode id (LayerRankSyntax.rank selection rankBound))
    (ForcingOrdinalTable.table (base labelSet) rankBound tab))))))))))))))))

theorem data_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain names r labelSet : Fin k)
    (base : Fin k → Fin n) (codes order group support fixing ranks selection rankBound tab : Fin n) :
    (data rho I G F mul q bound labels E root w chain names r labelSet base codes order group support fixing ranks selection rankBound tab).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
    ForcingTailGroup.tailGroup_freeClosed,ForcingCohenSelection.covariant_freeClosed,ForcingOrdinalTable.table_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain names r labelSet : Fin k)
    (base : Fin k → Fin n) (codes order group support fixing ranks selection rankBound tab : Fin n) :
    Project.Formula.satisfies env (data rho I G F mul q bound labels E root w chain names r labelSet base codes order group support fixing ranks selection rankBound tab) ↔
      Data hM (fun j => env.bound (base j)) rho I G F mul q bound labels E root w chain names r labelSet (env.bound codes) (env.bound order) (env.bound group) (env.bound support) (env.bound fixing) (env.bound ranks) (env.bound selection) (env.bound rankBound) (env.bound tab) := by
  have hLocal : (fun j : Fin (k+2) => env.bound (Fin.cases order (Fin.cases codes base) j)) =
      Fin.cases (env.bound order) (Fin.cases (env.bound codes) (fun j => env.bound (base j))) := by
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [data,Data,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingCohenSelection.covariant_semantics hM,ForcingCohenRankConsumers.monotone_semantics (M := M),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,id_eq,hLocal]
  rfl

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet : Fin k)
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
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
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
    (hRootCode : ConstructionComponentCarrier.Code (env root) (env r) (env index) (env U)) :
    ∃ codes order group support fixing ranks selection rankBound tab, Data hM env rho I G F mul q bound labels E root w chain names r labelSet codes order group support fixing ranks selection rankBound tab := by
  obtain ⟨codes,hCodes⟩ := ForcingTailCodes.exists_carrier hM env rho G F bound w names chain
  obtain ⟨order,hOrder⟩ := ConstructionGermPatternOrder.exists_order hM hChoice codes
  let other : Fin (k+2) → M.Carrier .set := Fin.cases order (Fin.cases codes env)
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  obtain ⟨group,support,fixing,ranks,selection,hGroup,hSupport,hFixing,hIncl,hSub,hMem,hCov,hMono,hRanks,hSelection,hFamily,hFixed⟩ :=
    ForcingCodeRanks.construct hM hChoice other (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up zero) (up root) (up vertices) (up chain) (up names) 1 0 (up r) (up index) (up U)
      hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hCodes hRootCode hOrder
  obtain ⟨rankBound,hRank⟩ := ForcingRawRank.exists_rank hM selection
  obtain ⟨tab,hTable⟩ := ForcingOrdinalTable.chooseTable hM hChoice (env labelSet) rankBound
    (ForcingGermDensity.ordinal_native (ForcingRawRank.rank_spec.mp hRank).1.1)
  exact ⟨codes,order,group,support,fixing,ranks,selection,rankBound,tab,hCodes,hOrder,hGroup,hSupport,hFixing,hIncl,hSub,hMem,hCov,hMono,hRanks,hSelection,hFamily,hFixed,hRank,hTable⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+9) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ
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
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
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
    (.imp (ConstructionComponentCarrier.code root r index U)
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (data rho I G F mul q bound labels E root w chain names r labelSet up 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,data_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet)).TrueIn M := by
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
    ConstructionComponentCarrier.code_semantics hM,data_semantics hM]
  exact construct hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet)).mp
      (construction_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names r index U labelSet hL hChoice)

end PPAC.Migration.ForcingOrbitCodeParameters
