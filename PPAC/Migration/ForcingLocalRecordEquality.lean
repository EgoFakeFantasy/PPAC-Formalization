/- Pinned LocalRecords.LocalWitness.equal_of_record_eq:143-182.
Same root index, label index and pulled-back condition; construct the root
permutation, move the actual witness, and reflect the equality to the root.
The covariant family is formula-indexed, matching the source hC hypothesis. -/
import PPAC.Migration.ForcingLocalRecordPullback
import PPAC.Migration.ForcingLocalInjectivity

namespace PPAC.Migration.ForcingLocalRecordEquality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (Small Injection)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportedNames (Range Supported)
open ForcingSupportingRoot (Code code_mem exists_code)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal source covariance, expressed using the original internal name action. -/
def Covariant {k : Nat} (family : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (fixing : M.Carrier .set) : Prop :=
  ∀ pi a i j ni nj, (Project.FirstOrderSemantics.reduct M).mem pi fixing →
    ForcingProductFamily.Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi a →
    MapRel family env i ni → MapRel family env j nj → PureKuratowski.PairMember M i j pi →
    ForcingStabilizer.Action (v 6) a ni nj

def covariant {k m : Nat} (family : Formula (k+2)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (fixing : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 5) (.bound fixing.succ.succ.succ.succ.succ.succ))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.action
      (rho 0).succ.succ.succ.succ.succ.succ (rho 1).succ.succ.succ.succ.succ.succ
      (rho 2).succ.succ.succ.succ.succ.succ (rho 3).succ.succ.succ.succ.succ.succ
      (rho 4).succ.succ.succ.succ.succ.succ (rho 5).succ.succ.succ.succ.succ.succ
      (rho 6).succ.succ.succ.succ.succ.succ 5 4))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family (fun n => (rr n).succ.succ.succ.succ.succ.succ) 3 1))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family (fun n => (rr n).succ.succ.succ.succ.succ.succ) 2 0))
    (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 3) (.bound 2) (.bound 5))
      (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6).succ.succ.succ.succ.succ.succ 4 1 0))))))))))))

theorem covariant_freeClosed {k m : Nat} (family : Formula (k+2)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (fixing : Fin m) : (covariant family rr rho fixing).FreeClosed := by
  simp -implicitDefEqProofs [covariant,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem covariant_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (family : Formula (k+2)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m) (fixing : Fin m)
    (env : Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (covariant family rr rho fixing) ↔
      Covariant family (fun n => env.bound (rr n)) (fun i => env.bound (rho i)) (env.bound fixing) := by
  simp only [covariant,Covariant,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.action_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),ForcingStabilizer.action_semantics (M := M)]
  rfl

/-- Construct the source root equality witness; neither name equality nor an action is assumed. -/
theorem equal_at_root (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (family : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B root s t b x i j A fixing
      d0 d1 pb z0 z1 sigma tau ni nj : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hroot : Injection (env (rho 0)) I root) (hs : Injection (env (rho 0)) I s) (ht : Injection (env (rho 0)) I t)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)))
    (hsroot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s b root)
    (htroot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) t b root)
    (hxi : PureKuratowski.PairMember M x i s) (hxj : PureKuratowski.PairMember M x j t)
    (hRange : Range (env (rho 0)) root A) (hFix : ForcingLabelPermutations.Fixing (env G) A fixing)
    (hSigma : Supported (fun n => env (rho n)) fixing sigma) (hTau : Supported (fun n => env (rho n)) fixing tau)
    (hCov : Covariant family env (fun n => env (rho n)) fixing)
    (hni : MapRel family env i ni) (hnj : MapRel family env j nj)
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) w d0)
    (hd1 : ForcingCohenConditions.Condition (env (rho 2)) w d1)
    (hds : ForcingLocalRecordPullback.Supported (env (rho 0)) s d0)
    (hdt : ForcingLocalRecordPullback.Supported (env (rho 0)) t d1)
    (hpb0 : ForcingLocalRecordPullback.Pullback (env (rho 0)) s d0 pb)
    (hpb1 : ForcingLocalRecordPullback.Pullback (env (rho 0)) t d1 pb)
    (hz0 : Code z0 d0 s) (hz1 : Code z1 d1 t)
    (he0 : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma ni z0)
    (he1 : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau nj z1) :
    ∃ dR zR, ConstructionCohenCompatibility.Restricted A d1 dR ∧
      ForcingCohenConditions.Condition (env (rho 2)) w dR ∧ Code zR dR root ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma tau zR := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hLarge : ¬ Small I mu := fun hi => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM I mu).mp hi)
  obtain ⟨pi,hpi,hmatch,hfix⟩ := ConstructionDiagramPlacements.permutation_over_root hM hChoice
    hw hMu hLarge hD hs ht (hm.2.1 b hb) hsroot htroot
  have hpiFix : (Project.FirstOrderSemantics.reduct M).mem pi fixing :=
    (hFix pi).mpr ⟨(hG pi).mpr hpi,fun y hy => hfix y ((hRange y).mp hy)⟩
  obtain ⟨a,ha⟩ := ForcingProductFamily.exists_action hM hpres hpi
  have hAction := (mapRel_action (fun n => env (rho n)) pi a).mpr ha
  have hfixSigma := hSigma pi hpiFix a hAction
  obtain ⟨_,i',hxi',hi'j⟩ := (hmatch x j).mp hxj
  have hij : PureKuratowski.PairMember M i j pi :=
    ForcingConditionGraphs.function_unique hs.1.1 hxi hxi' ▸ hi'j
  have hFamily := hCov pi a i j ni nj hpiFix ha hni hnj hij
  obtain ⟨f,g,hf,hfg,hg,hgg,him,hmove⟩ := ForcingLocalRecordPullback.transport hM hpres.1 hpres.2.1
    hs ht hpi hmatch hd0 hd1 hds hdt hpb0 hpb1
  have hMoved : ConstructionDescentPlacement.ActualMoved (env (rho 1)) (env (rho 2)) w pi d0 d1 :=
    ⟨f,g,hf,hfg,hg,hgg,hd1,him,hmove⟩
  have hzz := ForcingSupportingRoot.moved_code hM hpres ha hd0 hs ht hMoved hmatch hz0 hz1
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hPair : ∀ l : Fin 2, ForcingStabilizer.Action (env (rho 6)) a
      (args2 sigma ni l) (args2 sigma nj l) := by
    intro l
    exact Fin.cases hfixSigma (fun l => Fin.cases hFamily (fun l => Fin.elim0 l) l) l
  have hplaced : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma nj z1 :=
    (ForcingSeparation.symmetry hM env rho G F mul hpres hG hNormal hpi hAction
      (.equal (0 : Fin 2) 1) (args2 sigma ni) (args2 sigma nj) hPair (code_mem hpres hd0 hs hz0) hzz).mp he0
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have heq := ForcingAtomicLaws.eq_trans hM hpre hplaced (ForcingAtomicBasic.eq_symm hM he1)
  obtain ⟨dR,hdR,hR,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd1 A
  obtain ⟨zR,hzR⟩ := exists_code hM dR root
  have hsup : ∀ l : Fin 2, Supported (fun n => env (rho n)) fixing (args2 sigma tau l) := by
    intro l
    exact Fin.cases hSigma (fun l => Fin.cases hTau (fun l => Fin.elim0 l) l) l
  exact ⟨dR,zR,hR,hdR,hzR,ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot ht ⟨b,hb,htroot⟩ hd1 hRange hFix hR hz1 hzR
    (.equal (0 : Fin 2) 1) (args2 sigma tau) hsup heq⟩

theorem quotient_equal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (family : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B root s t b x i j A fixing
      d0 d1 pb z0 z1 sigma tau ni nj : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hroot : Injection (env (rho 0)) I root) (hs : Injection (env (rho 0)) I s) (ht : Injection (env (rho 0)) I t)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)))
    (hsroot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s b root)
    (htroot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) t b root)
    (hxi : PureKuratowski.PairMember M x i s) (hxj : PureKuratowski.PairMember M x j t)
    (hRange : Range (env (rho 0)) root A) (hFix : ForcingLabelPermutations.Fixing (env G) A fixing)
    (hSigma : Supported (fun n => env (rho n)) fixing sigma) (hTau : Supported (fun n => env (rho n)) fixing tau)
    (hCov : Covariant family env (fun n => env (rho n)) fixing)
    (hni : MapRel family env i ni) (hnj : MapRel family env j nj)
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) w d0)
    (hd1 : ForcingCohenConditions.Condition (env (rho 2)) w d1)
    (hds : ForcingLocalRecordPullback.Supported (env (rho 0)) s d0)
    (hdt : ForcingLocalRecordPullback.Supported (env (rho 0)) t d1)
    (hpb0 : ForcingLocalRecordPullback.Pullback (env (rho 0)) s d0 pb)
    (hpb1 : ForcingLocalRecordPullback.Pullback (env (rho 0)) t d1 pb)
    (hz0 : Code z0 d0 s) (hz1 : Code z1 d1 t)
    (he0 : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma ni z0)
    (he1 : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau nj z1)
    {g X pr alpha beta : M.Carrier .set}
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hd1g : (Project.FirstOrderSemantics.reduct M).mem d1 g)
    (hPr : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g root X pr)
    (hAlpha : PureKuratowski.PairMember M sigma alpha pr) (hBeta : PureKuratowski.PairMember M tau beta pr) :
    alpha = beta := by
  obtain ⟨dR,zR,hR,hdR,hzR,heq⟩ := equal_at_root hM hChoice family env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1
  have hdRg := hg.2.2.1 d1 dR hd1g ((hpres.2.2.1 dR).mpr hdR) (fun z hz => ((hR z).mp hz).1)
  exact (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hroot hPr
    sigma tau alpha beta hAlpha hBeta).mpr ⟨dR,zR,hdRg,hzR,heq⟩

def result {k m : Nat} (R : Formula (k+2)) (rr : Fin k → Fin m)
    (S W w A d root sigma tau : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ConstructionCohenCompatibility.restricted A.succ.succ d.succ.succ 1)
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 1))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 1 root.succ.succ))
      (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun n => (rr n).succ.succ)
        W.succ.succ sigma.succ.succ tau.succ.succ 0))))))

theorem result_freeClosed {k m : Nat} (R : Formula (k+2)) (rr : Fin k → Fin m)
    (S W w A d root sigma tau : Fin m) : (result R rr S W w A d root sigma tau).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenCompatibility.restricted_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (R : Formula (k+2)) (rr : Fin k → Fin m) (S W w A d root sigma tau : Fin m)
    (env : Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (result R rr S W w A d root sigma tau) ↔
      ∃ dR zR, ConstructionCohenCompatibility.Restricted (env.bound A) (env.bound d) dR ∧
        ForcingCohenConditions.Condition (env.bound S) (env.bound w) dR ∧ Code zR dR (env.bound root) ∧
        Forces true R (fun n => env.bound (rr n)) (env.bound W) (env.bound sigma) (env.bound tau) zR := by
  simp only [result,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionCohenCompatibility.restricted_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M)]
  rfl

def rootSentence {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection root (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection t (rho 0) I))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b root))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul t b root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge s x i))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge t x j))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) root A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A fixing))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing sigma))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing tau))
    (.imp (covariant family id rho fixing)
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family id i ni))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family id j nj))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d1))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d0)
    (.imp (ForcingLocalRecordPullback.supported (rho 0) t d1)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) s d0 pb)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) t d1 pb)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 s))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z1 d1 t))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma ni z0))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) tau nj z1))
    (result (orderFormula (rho 0) mul) id (rho 2) (rho 6) w A d1 root sigma tau))))))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
    Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
    ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
    covariant_freeClosed,ForcingLocalRecordPullback.supported_freeClosed,ForcingLocalRecordPullback.pullback_freeClosed,result_freeClosed]

theorem root_models {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence (rootSentence family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj) := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    covariant_semantics hM,ForcingMapConditions.rel_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingLocalRecordPullback.pullback_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),result_semantics hM]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1
  exact equal_at_root hM hChoice family bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1

theorem root_kernel_certificate {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj : Fin k) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (rootSentence family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let zero := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => zero⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact root_models family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj hL hChoice

def quotientSentence {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection root (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection t (rho 0) I))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b root))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul t b root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge s x i))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge t x j))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) root A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A fixing))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing sigma))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing tau))
    (.imp (covariant family id rho fixing)
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family id i ni))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel family id j nj))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d1))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d0)
    (.imp (ForcingLocalRecordPullback.supported (rho 0) t d1)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) s d0 pb)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) t d1 pb)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 s))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z1 d1 t))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma ni z0))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) tau nj z1))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (.mem (.bound d1) (.bound g))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g root X pr))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr sigma alpha))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr tau beta))
    (Project.Formula.extensionalEq (.bound alpha) (.bound beta))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
    Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
    ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
    covariant_freeClosed,ForcingLocalRecordPullback.supported_freeClosed,ForcingLocalRecordPullback.pullback_freeClosed]

theorem quotient_models {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence (quotientSentence family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta) := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    covariant_semantics hM,ForcingMapConditions.rel_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingLocalRecordPullback.pullback_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingLocalQuotient.projection_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1 hg hd1g hPr hAlpha hBeta
  exact quotient_equal hM hChoice family bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1 hg hd1g hPr hAlpha hBeta

theorem quotient_kernel_certificate {k : Nat} (family : Formula (k+2)) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta : Fin k) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (quotientSentence family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let zero := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => zero⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact quotient_models family rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta hL hChoice

end PPAC.Migration.ForcingLocalRecordEquality
