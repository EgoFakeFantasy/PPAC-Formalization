/- Pinned ClassFibers.outsideClassSet / outsideClassSet_denseBelow:255-306.
Consumer: ConcreteQuotients.nonwellorderable_quotient_bijection:401-443.
Keep the actual canonical quotient class, condition support coverage,
nontrivial right factor, and persistent exclusion from the ENTIRE local list.
Reuse the existing ideal-free outside-list theorem, support and diagram APIs. -/
import PPAC.Migration.ForcingUniformInverseGraph
import PPAC.Migration.ForcingAssignedGraphOnto

namespace PPAC.Migration.ForcingOutsideClassSet
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingProductFamily (actionFormula)
open ForcingSupportSize (Small Injection)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Witness {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K G F mul one q labelMap top bit labels E bound list : Fin k) (a : M.Carrier .set) : Prop :=
  ∃ t b At Ht z j cls,
    Injection (env (rho 0)) (env I) t ∧
    (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)) ∧ b ≠ env one ∧
    ForcingDiagramOrder.Sub (env (rho 0)) (env mul) t b (env q) ∧
    ForcingSupportedNames.Range (env (rho 0)) t At ∧
    ForcingLabelPermutations.Fixing (env G) At Ht ∧
    ConstructionCohenCompatibility.Within a At ∧ ForcingSupportingRoot.Code z a t ∧
    (Project.FirstOrderSemantics.reduct M).mem j At ∧
    MapRel (ForcingRelationClassMove.family rho G F mul I K labelMap top bit labels E) env j cls ∧
    ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) (env bound) Ht cls ∧
    ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) z cls (env list)

theorem denseBelow (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hq) (env E))
    (hEHS : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env E))
    (hNames : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) (env bound) (env Hq) (env names))
    (hAlpha : ForcingRawRank.Ordinal (env alpha))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo
      (KuratowskiZF.interpretation hM) (env enum) (env alpha) (env names))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env alpha) (env enum) (env (rho 6)) (env list))
    (hChecked : ForcingCheckName.Checked (env top) (env alpha) (env nalpha))
    (hY : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env Y))
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d0))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d0) (env q))
    (hnot : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args1 (env Y)) (env (rho 6)) (env z0) (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∀ d, ForcingCohenConditions.Condition (env (rho 2)) (env w) d → ForcingPowerName.Subset (env d0) d →
      ∃ a, ForcingCohenConditions.Condition (env (rho 2)) (env w) a ∧ ForcingPowerName.Subset d a ∧
        Witness env rho I K G F mul one q labelMap top bit labels E bound list a := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmallW : Small (env w) (env mu) := (ForcingSupportSize.native_small hM _ _).mpr hMu.2
  obtain ⟨dToMu,hdToMu⟩ := hCard.1
  have hSmallD : Small (env (rho 0)) (env mu) := (ForcingSupportSize.native_small hM _ _).mpr ⟨dToMu,hdToMu.1⟩
  have hLarge : ¬ Small (env I) (env mu) := by
    intro h
    exact hI.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  obtain ⟨Ar,hAr,hArI,hArSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hSmallD
  have hArA := ForcingCohenOrderAction.image_unique hM hAr hRange
  subst Ar
  have hHq := ForcingConjugationGraph.fixing_subgroup hM hG hFix hArI
  have hHqF := (hF (env Hq)).mpr ⟨hHq,env A,env Hq,hArI,hArSmall,hFix,fun _ h => h⟩
  obtain ⟨hYHS,hYFixed⟩ := ForcingQuotientName.hs_and_fixed hM env rho G F mul I K labelMap top bit labels E
    hp hG hF hw hMu hLabelMap hTop hLabels hEHS hY
  have hYSupport : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hq) (env Y) :=
    fun pi hpi a ha => hYFixed pi ((hFix pi).mp hpi).1 a ha (hE pi hpi a ha)
  have hz0W := ForcingSupportingRoot.code_mem hp hd0 hq hz0
  intro d hd hdd0
  obtain ⟨zp,hzp⟩ := ForcingSupportingRoot.exists_code hM d (env q)
  have hzpW := ForcingSupportingRoot.code_mem hp hd hq hzp
  have hzpz0 := (orderFormula_semantics env (rho 0) mul zp (env z0)).mpr
    ((ForcingSupportingRoot.code_le hzp hz0).mpr ⟨hdd0,ForcingDiagramPoset.le_refl hm hq⟩)
  obtain ⟨s,hs,hsp,y,_,hy,hout⟩ := ForcingUniformInverseGraph.outside_localList hM env rho
    I K B w G F Hq mul top bound names alpha enum list nalpha Y (env z0)
    hp hG hNormal hHq hHqF hTop hpre hNames hAlpha hEnum hList hChecked hYHS hYSupport hz0W hnot zp hzpW hzpz0
  obtain ⟨u,j,cls,hu,hus,hFamily,hyc⟩ :=
    ((ForcingQuotientName.mem_quotient hM env rho G F mul I K labelMap top bit labels E hY hpre hs).mp hy)
      s hs (hpre.1 s hs)
  obtain ⟨hj,hclsHS,xj,hxj,hcls⟩ :=
    (ForcingRelationClassMove.family_semantics env rho G F mul I K labelMap top bit labels E j cls).mp hFamily
  obtain ⟨a,root,c,ha,hRoot,hc,hcu⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hq hu
  have hcW := ForcingSupportingRoot.code_mem hp ha hRoot hc
  have hcu' := (orderFormula_semantics env (rho 0) mul c u).mpr hcu
  have hcp := hpre.2 c u zp hcW hu hzpW hcu' (hpre.2 u s zp hu hs hzpW hus hsp)
  have hBase := (ForcingSupportingRoot.code_le hc hzp).mp ((orderFormula_semantics env (rho 0) mul c zp).mp hcp)
  obtain ⟨support,hSupport,hSupportI,hSupportW⟩ := ConstructionCohenCompatibility.exists_support hM hw hp.1 hp.2.1 ha
  obtain ⟨sw,hsw⟩ := (ForcingSupportSize.native_small hM support (env w)).mp hSupportW
  obtain ⟨wm,hwm⟩ := hMu.2
  have hSupportMu := ZF.exists_compositionInjection hZF pair hsw hwm
  obtain ⟨single,hSingle⟩ := ForcingWithTopCarrier.exists_single hM j
  have hSingleMu := ForcingLabelNames.singleton_small hM hw hSmallW hSingle
  obtain ⟨cover,hUnion⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) support single
  have hCoverI : (Project.FirstOrderSemantics.reduct M).MemberSubset cover (env I) := by
    intro z hz
    rcases (hUnion z).mp hz with hz | hz
    · exact hSupportI z hz
    · exact ((hSingle z).mp hz).symm ▸ hj
  have hCoverMu : Small cover (env mu) := (ForcingSupportSize.native_small hM _ _).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu hSupportMu
      ((ForcingSupportSize.native_small hM _ _).mp hSingleMu) hUnion)
  obtain ⟨t,ht,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hRoot hCoverI hCoverMu
  have htr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) t root := ⟨env mark,hMark,hSub⟩
  obtain ⟨b,hb,hSubq⟩ := ForcingDiagramPoset.le_trans hm htr hBase.2
  obtain ⟨At,hAt,hAtI,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 ht hSmallD
  obtain ⟨Ht,hHt⟩ := ForcingLabelPermutations.exists_fixing hM (env G) At
  have hjT := (hAt j).mpr (hCover j ((hUnion j).mpr (Or.inr ((hSingle j).mpr rfl))))
  have hWithin : ConstructionCohenCompatibility.Within a At := by
    intro i k v he
    exact (hAt i).mpr (hCover i ((hUnion i).mpr (Or.inl ((hSupport i).mpr ⟨k,v,he⟩))))
  have hAAt : ForcingPowerName.Subset (env A) At := fun i hi =>
    (hAt i).mpr (ConstructionDescentPlacement.range_antitone ⟨b,hb,hSubq⟩ ((hRange i).mp hi))
  have hEt := ForcingSupportedNames.supported_mono hFix hHt hAAt hE
  let classEnv : Fin (k+1) → M.Carrier .set := Fin.cases xj env
  have heClass (i : Fin k) : classEnv i.succ = env i := rfl
  obtain ⟨tau,hLocal,htauClass',_⟩ := ForcingRelationClass.actual_labelClass hM classEnv
    (fun i => (rho i).succ) G.succ F.succ mul.succ labels.succ E.succ 0
    hw hMu hm hp hG hF hLabelMap hTop hLabels hxj hBound hAtI hHt hjT hEHS hEt
  have hRClass (v w : M.Carrier .set) :
      MapRel (orderFormula (rho 0).succ mul.succ) classEnv v w ↔ MapRel (orderFormula (rho 0) mul) env v w := by
    simp only [orderFormula_semantics,heClass]
  have hHClass (v : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun i => (rho i).succ) G.succ F.succ) classEnv v ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env v := by
    simp only [ForcingPairUnion.domain_semantics,heClass]
  have htauClass : ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env (env (rho 6)) (env labels) (env E) xj tau := by
    intro child z
    exact (htauClass' child z).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (ForcingEquivariantMix.forces_order_congr hRClass false (env (rho 6)) child (env labels) z)
        (ForcingSeparation.force_congr hRClass hHClass _ _ _ _))))
  have hclsEq := ForcingRelationClassMove.class_unique hM (ForcingHS.isName hclsHS)
    (ForcingHS.isName hLocal.1.1) hcls htauClass
  have hLocalCls : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) (env bound) Ht cls := hclsEq.symm ▸ hLocal
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM a t
  have hzW := ForcingSupportingRoot.code_mem hp ha ht hz
  have hzc := (orderFormula_semantics env (rho 0) mul z c).mpr
    ((ForcingSupportingRoot.code_le hz hc).mpr ⟨fun _ h => h,htr⟩)
  have hzu := hpre.2 z c u hzW hcW hu hzc hcu'
  have hzs := hpre.2 z u s hzW hu hs hzu hus
  have hOutside : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) z cls (env list) := by
    intro v hv hvz hmemb
    have hvu := hpre.2 v z u hv hzW hu hvz hzu
    exact hout v hv (hpre.2 v z s hv hzW hs hvz hzs)
      ((ForcingAtomicLaws.mem_congr_left hM hpre (ForcingAtomicBasic.eq_mono hM hpre hv hvu hyc)).mpr hmemb)
  have hbn : b ≠ env one := by
    intro he
    have htq : t = env q := ForcingDiagramPoset.injection_ext hM ht hq
      (fun x y => ((ForcingDiagramPoset.sub_one hm ht) x y).trans ((he ▸ hSubq) x y).symm)
    have hRangeqT : ForcingSupportedNames.Range (env (rho 0)) (env q) At := htq ▸ hAt
    have hAtA := ForcingCohenOrderAction.image_unique hM hRangeqT hRange
    have hHtq : ForcingLabelPermutations.Fixing (env G) (env A) Ht := hAtA ▸ hHt
    have hHteq := ForcingLabelPermutations.fixing_unique hM hHtq hFix
    have hLocalQ : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) (env bound) (env Hq) cls := hHteq ▸ hLocalCls
    exact hOutside z hzW (hpre.1 z hzW)
      (ForcingLocalList.localName_mem_localList hM (orderFormula (rho 0) mul) env (fun i => env (rho i))
        hpre hNames hEnum hList hzW hLocalQ)
  exact ⟨a,ha,hBase.1,t,b,At,Ht,z,j,cls,ht,hb,hbn,hSubq,hAt,hHt,hWithin,hz,hjT,hFamily,hLocalCls,hOutside⟩

def witness {k n : Nat} (rho : Fin 7 → Fin k)
    (I K G F mul one q labelMap top bit labels E bound list : Fin k)
    (base : Fin k → Fin n) (a : Fin n) : Project.Formula 1 n :=
  let up : Fin k → Fin (n+7) := fun i => (base i).succ.succ.succ.succ.succ.succ.succ
  let aa := a.succ.succ.succ.succ.succ.succ.succ
  let fields : List (Project.Formula 1 (n+7)) :=
    [ProjectSyntax.encode id (Source.SetLanguage.injection 6 (up (rho 0)) (up I)),
     .mem (.bound 5) (.bound (up (rho 0))),
     .neg (ProjectSyntax.encode id (Formula.equal 5 (up one))),
     ProjectSyntax.encode id (ForcingDiagramOrder.sub (up (rho 0)) (up mul) 6 5 (up q)),
     ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) 6 4),
     ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 4 3),
     ConstructionCohenCompatibility.within aa 4,
     ProjectSyntax.encode id (ForcingSupportingRoot.code 2 aa 6),
     .mem (.bound 1) (.bound 4),
     ProjectSyntax.encode id (ReplacementPredicates.rel
       (ForcingRelationClassMove.family rho G F mul I K labelMap top bit labels E) up 1 0),
     ProjectSyntax.encode id (ForcingLocalNames.localName (fun i => up (rho i)) (up G) (up F) (up bound) 3 0),
     ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) up (up (rho 6)) 2 0 (up list))]
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (fields.foldr (fun a b => .conj a b) (ProjectSyntax.encode id (Formula.equal (0 : Fin (n+7)) 0)))))))))

theorem witness_freeClosed {k n : Nat} (rho : Fin 7 → Fin k)
    (I K G F mul one q labelMap top bit labels E bound list : Fin k)
    (base : Fin k → Fin n) (a : Fin n) :
    (witness rho I K G F mul one q labelMap top bit labels E bound list base a).FreeClosed := by
  simp -implicitDefEqProofs [witness,List.foldr,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,ConstructionCohenCompatibility.within_freeClosed]

theorem witness_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k)
    (I K G F mul one q labelMap top bit labels E bound list : Fin k)
    (base : Fin k → Fin n) (a : Fin n) :
    Project.Formula.satisfies env (witness rho I K G F mul one q labelMap top bit labels E bound list base a) ↔
      Witness (fun i => env.bound (base i)) rho I K G F mul one q labelMap top bit labels E bound list (env.bound a) := by
  simp only [witness,Witness,List.foldr,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ConstructionCohenCompatibility.within_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingLocalNames.localName_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M),Formula.Realize,and_true]
  rfl

def densityResult {k : Nat} (rho : Fin 7 → Fin k)
    (I K G F mul one q labelMap top bit labels E bound list w d0 : Fin k) : Project.Formula 1 k :=
  .forallE ((ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ w.succ 0)).imp
    ((ProjectSyntax.encode id (Source.SetLanguage.subset d0.succ 0)).imp
      (.existsE ((ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 0)).conj
        ((ProjectSyntax.encode id (Source.SetLanguage.subset 1 0)).conj
          (witness rho I K G F mul one q labelMap top bit labels E bound list (fun i => i.succ.succ) 0))))))

def premises {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 : Fin k) :
    List (Project.Formula 1 k) :=
  [Project.Formula.isOmega (.bound w),
   Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
   ConstructionSaturationIndex.hartogs mu I,
   ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one),
   ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu,
   .mem (.bound mark) (.bound (rho 0)),
   ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
   ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels),
   ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound),
   ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I),
   ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A),
   ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq),
   ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E),
   ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hq names),
   ProjectSyntax.encode id (OrdinalSyntax.ordinal alpha),
   Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound alpha) (.bound names),
   ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 alpha enum (rho 6) list),
   ProjectSyntax.encode id (ForcingCheckName.checkName top alpha nalpha),
   ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id Y),
   ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0),
   ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 q),
   ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
     id (Source.SetLanguage.args1 Y) (rho 6) z0 (ForcingCheckOrdinal.wellorderable 0).neg)]

def densitySentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ((premises rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0).foldr
      (fun a b => .imp a b) (densityResult rho I K G F mul one q labelMap top bit labels E bound list w d0))
  freeClosed := by
    simp -implicitDefEqProofs [premises,densityResult,List.foldr,Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,witness_freeClosed]

theorem density_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (densitySentence rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingLocalNames.carrier_semantics (M := M),ForcingRawRank.ordinal_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingQuotientName.quotient_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingFormula.formula_semantics (M := M),id_eq]
  intro hw hMu hI hm hCard hMark hp hG hF hMap hTop hLabels hBound hq hRange hFix hE hEHS hNames hAlpha hEnum hList hChecked hY hd0 hz0 hnot
  have harg : (fun i => env (Source.SetLanguage.args1 Y i)) = Source.SetLanguage.args1 (env Y) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [harg] at hnot
  simp only [densityResult,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),witness_semantics hM]
  exact denseBelow hM hChoice env rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0
    hw hMu hI hm hCard hMark hp hG hF hMap hTop hLabels hBound hq hRange hFix hE hEHS hNames hAlpha hEnum hList hChecked hY hd0 hz0 hnot

theorem density_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (densitySentence rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0))) := by
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
  apply ConstructibleGround.relative_models hM
    (densitySentence rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (densitySentence rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0)).mp
    (density_models rho I K B w G F mul one mu mark q A Hq labelMap top bit labels E bound names alpha enum list nalpha Y d0 z0 hL hChoice)

end PPAC.Migration.ForcingOutsideClassSet
