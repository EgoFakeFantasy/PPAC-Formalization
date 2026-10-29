/- Pinned CodeLinks:106-143. The four consumers use the SAME generated
rank history/type, before universally quantifying over internal conditions. -/
import PPAC.Migration.ForcingCodeRanks

namespace PPAC.Migration.ForcingCodeRankConsumers
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula)
open ForcingCodeSelection (IsSelected relation mapRel_relation)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

open ForcingCohenSelection (liftRelation)
open ForcingCohenRankConsumers (typeDecision lowerDecision memberDecision)
open ForcingAtomicRelations (forces)
open ForcingSupportingRoot (code)
open ForcingCheckName (checkName)

def consumerResult {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (mul w root d X ranks selection top z a b na nb theta ntheta beta nbeta : Fin k) : Formula k :=
  let L := orderFormula (rho 0) mul
  let sa := ForcingOrdinalCoding.selectedInput R rp X ranks a na d
  let sb := ForcingOrdinalCoding.selectedInput R rp X ranks b nb d
  (typeDecision L id (rho 6) (rho 2) w top selection root d).conj
    ((sa.imp ((forces false L id (rho 6) na selection z).conj
      (sb.imp ((forces true L id (rho 6) na nb z).iff (.equal a b))))).conj
    ((checkName top theta ntheta).imp ((forces true L id (rho 6) selection ntheta z).imp
      ((sa.imp (lowerDecision L id (rho 6) (rho 2) w top na root d theta)).conj
        ((checkName top beta nbeta).imp ((Formula.mem beta theta).imp
          (memberDecision L id R rp (rho 6) (rho 2) w X ranks root d nbeta)))))))

def allConsumers {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (mul w root X ranks selection top : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+10) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 9))
      (.imp (ProjectSyntax.encode id (code 8 9 (up root)))
        (ProjectSyntax.encode id (consumerResult R (fun j => up (rp j)) (fun j => up (rho j))
          (up mul) (up w) (up root) 9 (up X) (up ranks) (up selection) (up top) 8 7 6 5 4 3 2 1 0)))))))))))))

theorem allConsumers_freeClosed {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (mul w root X ranks selection top : Fin k) :
    (allConsumers R rp rho mul w root X ranks selection top).FreeClosed := by
  simp -implicitDefEqProofs [allConsumers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

private theorem consume {k n : Nat} (R : Formula (n+2)) (rp : Fin n → Fin k) (rho : Fin 7 → Fin k)
    (w mu tower kappa unit mark H C incoming base I K B G F mul root d A fixing support X order ranks selection top z
      a b na nb theta ntheta beta nbeta : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k)
    (hCtx : Project.Formula.satisfies env (ForcingOrdinalRoot.rootContext rho w mu tower kappa unit mark H C incoming base I K B G F mul root A fixing))
    (hCov : ForcingCohenSelection.Covariant R (fun j => env.bound (rp j)) (env.bound (rho 2)) (env.bound w) (env.bound support) (env.bound X))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env.bound order) (env.bound X))
    (hSub : ForcingConjugationGraph.Subgroup (env.bound I) (env.bound G) (env.bound support))
    (hMem : (Project.FirstOrderSemantics.reduct M).mem (env.bound support) (env.bound F))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound fixing) (env.bound support))
    (hTop : ForcingWithTopCarrier.Empty (env.bound top))
    (hd : ForcingCohenConditions.Condition (env.bound (rho 2)) (env.bound w) (env.bound d))
    (hz : ForcingSupportingRoot.Code (env.bound z) (env.bound d) (env.bound root))
    (hRanks : ForcingOrdinalRanks.Ranks (liftRelation R rp (rho 0) I (rho 2) w) env.bound (env.bound X) (env.bound order) (env.bound (rho 6)) (env.bound ranks))
    (hType : ForcingCollectedName.Collected (liftRelation R rp (rho 0) I (rho 2) w) env.bound (env.bound X) (env.bound ranks) (env.bound (rho 6)) (env.bound selection))
    (hMono : ForcingCohenRankConsumers.Monotone R (fun j => env.bound (rp j)) (env.bound (rho 2)) (env.bound w) (env.bound X)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env.bound
      (consumerResult R rp rho mul w root d X ranks selection top z a b na nb theta ntheta beta nbeta) := by
  have hAll := (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mp
    (ForcingCohenRankConsumers.construction_models R rp rho w mu tower kappa unit mark H C incoming base I K B G F mul
      root d A fixing support X order ranks selection top z a b na nb theta ntheta beta nbeta hM hChoice) env.free
  have h := (Project.Formula.satisfies_forallClosure_iff env.free _).mp hAll env.bound
  simp only [Project.Formula.satisfies_imp_iff,ForcingCohenSelection.covariant_semantics hM,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Term.eval_bound] at h
  have hb := h hCtx hCov hOrder
  simp only [ForcingCohenRankConsumers.consumerBody,Formula.Realize,
    ForcingConjugationGraph.subgroup_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),ForcingCohenRankConsumers.monotone_semantics (M := M)] at hb
  have hh := hb ⟨hSub,hMem,hIncl,hTop,hd,hz,hRanks,hType⟩
  simp only [consumerResult,Formula.Realize]
  exact ⟨hh.1,hh.2.1,fun ht hf => ⟨(hh.2.2 ht hf).1, (hh.2.2 ht hf).2 hMono⟩⟩
def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k) : Project.Sentence where
  formula :=
    let R := relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    let up : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
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
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r index U)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingTailGroup.tailGroup (up w) (up (rho 0)) (up G) (up chain) 4)
      (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) (up r) 3))
      (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 3 2))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset 2 4))
      (.conj (ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (up I) (up G) 4))
      (.conj (.mem (.bound 4) (.bound (up F)))
      (.conj (ForcingCohenSelection.covariant R up (up (rho 2)) (up w) 4 (up codes))
      (.conj (ProjectSyntax.encode id (ForcingCohenRankConsumers.monotone R up (up (rho 2)) (up w) (up codes)))
      (.conj (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L up (up codes) (up order) (up (rho 6)) 1))
      (.conj (ProjectSyntax.encode id (ForcingCollectedName.collected L up (up codes) 1 (up (rho 6)) 0))
      (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily (fun j => up (rho j)) (up G) (up F) 4 (up codes) 1))
      (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => up (rho j)) (up G) (up F) 4 0))
      (allConsumers R up (fun j => up (rho j)) (up mul) (up w) (up r) (up codes) 1 0 (up top))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailGroup.tailGroup_freeClosed,ForcingCohenSelection.covariant_freeClosed,
      Project.Formula.isSetCodedWellOrder_freeClosed,allConsumers_freeClosed]
theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
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
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingTailGroup.tailGroup_semantics hM,ForcingLabelPermutations.subset_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),ForcingCohenSelection.covariant_semantics hM,
    ForcingCohenRankConsumers.monotone_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M)]
  intro hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hCarrier hRootCode hOrder
  obtain ⟨group,support,fixing,ranks,selection,hGroup,hRange,hFix,hInclude,hSub,hMember,hCov,hMono,hRanks,hType,hFamily,hFixed⟩ :=
    ForcingCodeRanks.construct hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U
      hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hCarrier hRootCode hOrder
  refine ⟨group,support,fixing,ranks,selection,hGroup,hRange,hFix,hInclude,hSub,hMember,hCov,hMono,hRanks,hType,hFamily,hFixed,?_⟩
  simp only [allConsumers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M)]
  intro d z a b na nb theta ntheta beta nbeta hd hz
  let up : Fin k → Fin (k+15) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  apply consume _ _ _ _ (up mu) (up history)
    (up kappa) (up one)
    (up mark) (up H) (up C)
    (up incoming) (up base)
    (up I) (up K) (up B)
    (up G) (up F) _ _ _ 13 12 14 _
    (up order) _ _ _ _ _ _ _ _ _ _ _ _ hM hChoice
    ⟨_,free⟩
  · simp only [ForcingOrdinalRoot.rootContext,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_isOmega_iff,
      Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
      ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
      ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
      ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
      ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
      ForcingStabilizerTransport.image_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
      Project.Term.eval_bound,up,Fin.cases_succ]
    exact ⟨hw,hMu,hI,hSmallD,hMergers,hRow,hm,hp,hG,hF,(ForcingTailGroup.root_vertex hChain hRootCode).1,hRange,hFix⟩
  · exact hCov
  · exact hOrder
  · exact hSub
  · exact hMember
  · exact hInclude
  · exact hTop
  · exact hd
  · exact hz
  · simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,ForcingCohenSelection.mapRel_lift,
      SetTheory.Env.push,up,Fin.cases_succ,Fin.cases_zero,id_eq,
      show (1 : Fin (k+5)) = (0 : Fin (k+4)).succ from rfl] using hRanks
  · simpa only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
      ForcingCohenSelection.mapRel_lift,SetTheory.Env.push,up,Fin.cases_succ,Fin.cases_zero,id_eq,
      show (1 : Fin (k+5)) = (0 : Fin (k+4)).succ from rfl] using hType
  · exact hMono
theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)).mp
      (construction_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U hL hChoice)

end PPAC.Migration.ForcingCodeRankConsumers
