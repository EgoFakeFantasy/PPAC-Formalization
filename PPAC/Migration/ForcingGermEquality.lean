/- Pinned GermSelectors.ordinal_value_unique:76 and preliminary_eq_iff:86.
The SAME actual Selected relation, generated rank history and fixed table are
consumed; no arbitrary rank-injectivity assumption or replacement relation. -/
import PPAC.Migration.ForcingGermPreliminary

namespace PPAC.Migration.ForcingGermEquality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPrincipalFilter (EqF)
open ForcingGermPreliminary (Preliminary preliminary)
open ForcingCheckName (Checked)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem checked_value_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one d r top name theta psi ntheta npsi : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (ht : ForcingWithTopCarrier.Empty top)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hTheta : Checked top theta ntheta) (hPsi : Checked top psi npsi)
    (heTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r name ntheta)
    (hePsi : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r name npsi) : theta = psi := by
  obtain ⟨z,_,he⟩ := ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr
    (ForcingPrincipalFilter.eqF_symm hM heTheta) hePsi
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact (ForcingCheckReflection.eq_check_iff hM hpre ((hp.2.2.2.2.2 top).mpr (Or.inl ht))
    (fun q _ => (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht))
    (ForcingAtomicBasic.condition hM he) hTheta hPsi).mp he

theorem preliminary_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group : Fin k)
    {d vertex localRoot index U label other tau sigma : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hc : ConstructionComponentCarrier.Code vertex localRoot index U)
    (hA : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau)
    (hB : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex other sigma) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d localRoot tau sigma ↔ label = other := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := hA
  obtain ⟨hk,hSigma,psi,b,nb,npsi,gamma,ngamma,hElig',hb,hRank',hIndex',hPsi,hGamma,hSel',hEqT',hEqR',hLink'⟩ := hB
  have hr := (ForcingTailGroup.root_vertex hChain hRoot).1
  have heTheta := checked_value_unique hM env rho mul hm hp hTop hd hr hTheta hPsi hEqT hEqT'
  subst psi
  obtain ⟨f,hBij,hIndices⟩ := ForcingOrdinalTable.indices_bijection hM hTable hElig
  have hfa := (hIndices label beta).mp hIndex
  have hfb := (hIndices other gamma).mp hIndex'
  have haCode := (hCarrier a).mp ha
  have hbCode := (hCarrier b).mp hb
  have hLinks := ForcingCodeLinks.links_eq_iff_same hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF hChain hd hc haCode hbCode hLink hLink'
  constructor
  · intro he
    have hab := ForcingPersistentSelection.selected_unique (L := fun p q => ForcingPowerName.Subset q p)
      (E := ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain)) hM hOrder
      (fun _ _ _ _ _ _ hs => ForcingPersistentCodes.same_symm hM hs)
      hd (fun _ hx => hx) ha hb hSel hSel' (hLinks.mp he)
    subst b
    have hNames := ForcingConditionGraphs.function_unique hRanks.1 hRank hRank'
    subst nb
    have hValues := checked_value_unique hM env rho mul hm hp hTop hd hr hBeta hGamma hEqR hEqR'
    subst gamma
    exact hBij.1.2 label other beta hfa hfb
  · intro hLabels
    subst other
    have hValues := hBij.1.1.1.2 label beta gamma hfa hfb
    subst gamma
    have hCheck := ForcingCheckName.unique hM hBeta hGamma
    subst ngamma
    obtain ⟨z,hz,hRankEq⟩ := ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr hEqR
      (ForcingPrincipalFilter.eqF_symm hM hEqR')
    have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
    have htP := (hp.2.2.2.2.2 (env top)).mpr (Or.inl hTop)
    have htop : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6)) →
        ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env z (env top) :=
      fun z _ => (orderFormula_semantics env (rho 0) mul z (env top)).mpr (Or.inl hTop)
    have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
    have hdomain := fun name => ForcingPairUnion.domain_semantics env rho G F name
    have hcheck : ∀ x nx, Checked (env top) x nx →
        ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env nx := by
      intro x nx hn
      exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun j => env (rho j)) hp hG hNormal hTop hn)
    have hLift (a : M.Carrier .set)
        (hsa : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a d) :
        ForcingMapConditions.MapRel
          (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) env a z := by
      apply (ForcingCohenSelection.mapRel_lift _ id env (rho 0) I (rho 2) w a z).mpr
      apply (ForcingCohenSelection.lift_coe ((hp.2.2.1 d).mp hd) hr hz).mpr
      exact (ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a d).mpr hsa
    have hab := (ForcingOrdinalCoding.selectedRank_eq_iff hM hpre htP htop hdomain hcheck hOrder hRanks ha hb hRank hRank'
      ((hdomain na).mpr (hFamily a ha na hRank).1) ((hdomain nb).mpr (hFamily b hb nb hRank').1)
      (ForcingAtomicBasic.condition hM hRankEq) (hLift a hSel) (hLift b hSel')).mp hRankEq
    subst b
    exact hLinks.mpr (ForcingPersistentCodes.same_refl hM env rho mul hm hp hw hChain haCode.1 hd)


def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ConstructionComponentCarrier.code vertex localRoot index U)
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label tau)
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex other sigma)
    (.iff (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
      (Project.Formula.extensionalEq (.bound label) (.bound other)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingTailCodes.carrier_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingGermPreliminary.preliminary_freeClosed,
      ForcingPrincipalFilter.eqF_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingGermPreliminary.preliminary_semantics hM,ForcingPrincipalFilter.eqF_semantics hM]
  exact preliminary_eq_iff hM hChoice env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (equalitySentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma)).mp
      (equality_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group d vertex localRoot index U label other tau sigma hL hChoice)

end PPAC.Migration.ForcingGermEquality
