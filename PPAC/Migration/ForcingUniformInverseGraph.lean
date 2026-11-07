/- Pinned UniformNames.UniformInverse.least_move/relation_move:212-233,
uniformRangeInverse / uniformSubsetInverse:239-279.
Consumer: outside_uniformRange -> ClassFibers.outside_localList ->
outsideClassSet_denseBelow -> ConcreteQuotients.nonwellorderable_quotient_bijection.
Reuse actual Product actions, check-name mapping, and the existing HS graph. -/
import PPAC.Migration.ForcingUniformInverse
import PPAC.Migration.ForcingRelationGraphFunctions
import PPAC.Migration.ForcingOutsideLocal

namespace PPAC.Migration.ForcingUniformInverseGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingStabilizer (Action)
open ForcingUniformInverse (LeastValue Holds)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem least_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w X f pi a p p' x x' i : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hfix : ∀ j fj, (Project.FirstOrderSemantics.reduct M).mem j X →
      PureKuratowski.PairMember M j fj f → Action (env (rho 6)) a fj fj)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpp : PureKuratowski.PairMember M p p' a) (hxx : Action (env (rho 6)) a x x')
    (hi : LeastValue (orderFormula (rho 0) mul) env (env (rho 6)) X f p x i) :
    LeastValue (orderFormula (rho 0) mul) env (env (rho 6)) X f p' x' i := by
  have hdata := (mapRel_action _ _ _).mp ha
  have har := ForcingProductFamily.action_permutation hdata
  have ho := ForcingProductFamily.order hM (env mul) hp hpi hdata
  have heq (j fj t t' : M.Carrier .set)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j X) (hfj : PureKuratowski.PairMember M j fj f)
      (ht : (Project.FirstOrderSemantics.reduct M).mem t (env (rho 6)))
      (htt : PureKuratowski.PairMember M t t' a) :
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x fj t ↔
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x' fj t' :=
    ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha (.equal (0 : Fin 2) 1)
      (args2 x fj) (args2 x' fj)
      (fun z => Fin.cases hxx (fun z => Fin.cases (hfix j fj hj hfj) (fun z => Fin.elim0 z) z) z) ht htt
  obtain ⟨fi,hfi,hei⟩ := hi.2.2.1
  refine ⟨hi.1,hi.2.1,⟨fi,hfi,(heq i fi p p' hi.2.1 hfi hpW hpp).mp hei⟩,?_⟩
  intro j fj hj hji hfj q' hq' hqp' he
  obtain ⟨q,hq,hqq⟩ := har.2.2 q' hq'
  have hqp : MapRel (orderFormula (rho 0) mul) env q p :=
    (orderFormula_semantics env (rho 0) mul q p).mpr
      ((ho q p q' p' hqq hpp).mpr ((orderFormula_semantics env (rho 0) mul q' p').mp hqp'))
  exact hi.2.2.2 j fj hj hji hfj q hq hqp ((heq j fj q q' hj hfj hq hqq).mpr he)

theorem checked_fixed (hM : FirstOrder.Theory.Models M nativeZF)
    {W a top i ni : M.Carrier .set} (ha : ForcingConditionGraphs.Endomap W a)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top W)
    (htt : PureKuratowski.PairMember M top top a) (hni : ForcingCheckName.Checked top i ni) :
    Action W a ni ni := by
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM ha ni
  have hfn := ForcingConditionAction.act_function (args2 W a) (0 : Fin 2) 1 ha
  have htop := (ForcingConditionAction.relation_semantics (args2 W a) (0 : Fin 2) 1 top top).mpr
    (Or.inl ⟨ht,htt⟩)
  have hnout := ForcingCheckNameLaws.map_checked hM
    (ForcingConditionAction.actFormula (0 : Fin 2) 1) (args2 W a) hfn top top htop i ni out hni
      ((ForcingNameConjugacy.action_iff (args2 W a) (0 : Fin 2) 1 ni out).mpr hout)
  exact ForcingCheckName.unique hM hnout hni ▸ hout

theorem relation_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w X f top pi a p p' x x' y y' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (ht : ForcingWithTopCarrier.Empty top)
    (hfix : ∀ j fj, (Project.FirstOrderSemantics.reduct M).mem j X →
      PureKuratowski.PairMember M j fj f → Action (env (rho 6)) a fj fj)
    (_hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpp : PureKuratowski.PairMember M p p' a) (hxx : Action (env (rho 6)) a x x')
    (hyy : Action (env (rho 6)) a y y')
    (h : Holds (orderFormula (rho 0) mul) env (env (rho 6)) X f top p x y) :
    Holds (orderFormula (rho 0) mul) env (env (rho 6)) X f top p' x' y' := by
  have hdata := (mapRel_action _ _ _).mp ha
  have har := ForcingProductFamily.action_permutation hdata
  have ho := ForcingProductFamily.order hM (env mul) hp hpi hdata
  have htW := (hp.2.2.2.2.2 top).mpr (Or.inl ht)
  intro q' hq' hqp'
  obtain ⟨q,hq,hqq⟩ := har.2.2 q' hq'
  have hqp : MapRel (orderFormula (rho 0) mul) env q p :=
    (orderFormula_semantics env (rho 0) mul q p).mpr
      ((ho q p q' p' hqq hpp).mpr ((orderFormula_semantics env (rho 0) mul q' p').mp hqp'))
  obtain ⟨r,hr,hrq,i,ni,hni,hyi,hi⟩ := h q hq hqp
  obtain ⟨r',hrr,_⟩ := har.1.1.2 r hr
  have hr' := har.1.2 r r' hrr
  have hrq' : MapRel (orderFormula (rho 0) mul) env r' q' :=
    (orderFormula_semantics env (rho 0) mul r' q').mpr
      ((ho r q r' q' hrr hqq).mp ((orderFormula_semantics env (rho 0) mul r q).mp hrq))
  have hfixed := checked_fixed hM har.1 htW (ForcingProductFamily.top_fixed hp ht hdata) hni
  have hyi' : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y' ni r' :=
    (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha (.equal (0 : Fin 2) 1)
      (args2 y ni) (args2 y' ni)
      (fun z => Fin.cases hyy (fun z => Fin.cases hfixed (fun z => Fin.elim0 z) z) z) hr hrr).mp hyi
  exact ⟨r',hr',hrq',i,ni,hni,hyi',least_move hM env rho G F mul hp hG hF hpi ha hfix hr hrr hxx hi⟩

def relation {k : Nat} (rho : Fin 7 → Fin k) (mul X f top : Fin k) : Formula (k+3) :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  ForcingUniformInverse.holds (orderFormula (rho 0) mul) up (up (rho 6)) (up X) (up f) (up top)
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (mul X f top : Fin k) (p x y : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds (relation rho mul X f top) env p x y ↔
      Holds (orderFormula (rho 0) mul) env (env (rho 6)) (env X) (env f) (env top) p x y := by
  unfold ForcingRelationGraphForcing.Holds relation
  simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using
    ForcingUniformInverse.holds_semantics (M := M) (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env)))
      (orderFormula (rho 0) mul) (fun j => j.castSucc.castSucc.castSucc)
      (rho 6).castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc
      f.castSucc.castSucc.castSucc top.castSucc.castSucc.castSucc
      (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem relation_moves (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F H mul X f top : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hfix : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env H) (env X) (env f)) :
    ForcingRelationGraphSupport.Moves (relation rho mul X f top) env rho G F H := by
  intro pi hpi a ha p p' x y x' y' hpW hpp _ _ hxx hyy hrel
  apply (relation_semantics env rho mul X f top p' x' y').mpr
  exact relation_move hM env rho G F mul hp hG hF ((hG pi).mp (hH.1 pi hpi)) ha ht
    (fun j fj hj hfj => (hfix j hj fj hfj).2 pi hpi a ha) hpW hpp hxx hyy
    ((relation_semantics env rho mul X f top p x y).mp hrel)

theorem monotone {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X f top : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    ForcingRelationGraphForcing.Monotone (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul X f top)
      env (env (rho 6)) (env G) (env F) := by
  intro p q x y hp hq hqp _ _ h
  exact (relation_semantics env rho mul X f top q x y).mpr
    (ForcingUniformInverse.relation_mono hpre hp hq hqp
      ((relation_semantics env rho mul X f top p x y).mp h))

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul X f top : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    ForcingRelationGraphForcing.Congruent (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul X f top)
      env (env (rho 6)) (env G) (env F) := by
  intro p x y x' y' _ _ _ _ hxx hyy
  exact (relation_semantics env rho mul X f top p x y).trans
    ((ForcingUniformInverse.relation_congr hM hpre hxx hyy).trans
      (relation_semantics env rho mul X f top p x' y').symm)

theorem regular {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X f top : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    ForcingRelationGraphForcing.Regular (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul X f top)
      env (env (rho 6)) (env G) (env F) := by
  intro p x y _ _ _ hd
  apply (relation_semantics env rho mul X f top p x y).mpr
  apply ForcingUniformInverse.relation_regular hpre
  intro q hq hqp
  obtain ⟨r,hr,hrq,hh⟩ := hd q hq hqp
  exact ⟨r,hr,hrq,(relation_semantics env rho mul X f top r x y).mp hh⟩

/-- Pinned uniformSubsetInverse_injection. Construct the actual HS graph
using its literal least-value relation; consume membership in the SAME list.
For Y = list the subset premise is reflexive (uniformRangeInverse_injection). -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y : Fin k) (p : M.Carrier .set)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (hHF : (Project.FirstOrderSemantics.reduct M).mem (env H) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hNames : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env H) (env names))
    (hAlpha : ForcingRawRank.Ordinal (env alpha))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo
      (KuratowskiZF.interpretation hM) (env enum) (env alpha) (env names))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env alpha) (env enum) (env (rho 6)) (env list))
    (hChecked : ForcingCheckName.Checked (env top) (env alpha) (env nalpha))
    (hY : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hfixY : ForcingSupportedNames.Supported (fun j => env (rho j)) (env H) (env Y))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hsub : ∀ x, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p →
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) q →
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env list) q) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relation rho mul alpha enum top)
        env (rho 6) top Y nalpha graph ∧
      ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) (env H) graph ∧
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 graph (env Y) (env nalpha)) (env (rho 6)) p
        (Source.SetLanguage.injection 0 1 2) := by
  have htW := (hp.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have htop (q : M.Carrier .set) (_ : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6))) :
      MapRel (orderFormula (rho 0) mul) env q (env top) :=
    (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hNA := ForcingInfinity.check_hs hM (fun j => env (rho j)) hp hG hF ht hChecked
  have hfixNA : ForcingSupportedNames.Supported (fun j => env (rho j)) (env H) (env nalpha) := by
    intro pi _ a ha
    have hdata := (mapRel_action _ _ _).mp ha
    exact checked_fixed hM (ForcingProductFamily.action_permutation hdata).1 htW
      (ForcingProductFamily.top_fixed hp ht hdata) hChecked
  have hfix : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env H) (env alpha) (env enum) := by
    intro i hi name hin
    have hn := (hNames name).mp (hEnum.1.1.output_mem_of_pairMember hin)
    exact ⟨hn.1.1,hn.2⟩
  obtain ⟨graph,hGraph,hGraphHS,hGraphFixed⟩ := ForcingRelationGraphSupport.construct hM
    (relation rho mul alpha enum top) env rho I K B w G F H mul top Y nalpha
    hp hG hF hH ht hY hNA hfixY hfixNA
    (relation_moves hM env rho I K B w G F H mul alpha enum top hp hG hF hH ht hfix) hHF
  refine ⟨graph,hGraph,hGraphHS,hGraphFixed,?_⟩
  have htotal : ForcingRelationGraphFunctions.Total (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul alpha enum top)
      env (env (rho 6)) (env G) (env F) (env Y) (env nalpha) p := by
    intro x hx q hq hqp hm r hr hrq
    have hxlist := hsub x ((ForcingRelationGraphApplication.hs_actionAt env rho (env G) (env (rho 6)) (env F) x).mp hx) q hq hqp hm
    obtain ⟨s,hs,hsr,y,hy,hh⟩ := ForcingUniformInverse.relation_total hM
      (orderFormula (rho 0) mul) env (fun j => env (rho j)) hpre htW htop
      hNames hAlpha hEnum hList hChecked hq hxlist r hr hrq
    obtain ⟨t,htc,hts,i,ni,hni,he,hi⟩ := hh s hs (hpre.1 s hs)
    have hniHS := ForcingInfinity.check_hs hM (fun j => env (rho j)) hp hG hF ht hni
    have hmem := (ForcingAtomicLaws.mem_congr_left hM hpre he).mp
      (ForcingAtomicBasic.mem_mono hM hpre htc hts hy)
    refine ⟨t,htc,hpre.2 t s r htc hs hr hts hsr,ni,
      (ForcingRelationGraphApplication.hs_actionAt env rho (env G) (env (rho 6)) (env F) ni).mpr hniHS,hmem,?_⟩
    apply (relation_semantics env rho mul alpha enum top t x ni).mpr
    intro u hu hut
    exact ⟨u,hu,hpre.1 u hu,i,ni,hni,ForcingAtomicBasic.eq_refl hM hpre ni u hu,
      ForcingUniformInverse.least_mono hM hpre hu hut hi⟩
  have hone : ForcingRelationGraphFunctions.One (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul alpha enum top)
      env (env (rho 6)) (env G) (env F) p := by
    intro q hq _ x y z _ _ _ hy hz
    exact ForcingUniformInverse.relation_one hM hpre hq
      ((relation_semantics env rho mul alpha enum top q x y).mp hy)
      ((relation_semantics env rho mul alpha enum top q x z).mp hz)
  have hfunc := ((ForcingSupportSize.native_mapsTo hM (env alpha) (env names) (env enum)).mpr hEnum.1.1).1
  have hinj : ForcingRelationGraphFunctions.Injective (orderFormula (rho 0) mul)
      (ForcingRelationGraphApplication.actionAt rho) (relation rho mul alpha enum top)
      env (env (rho 6)) (env G) (env F) p := by
    intro q hq _ x y z _ _ _ hx hy
    exact ForcingUniformInverse.relation_inj hM hpre htW htop hfunc hq
      ((relation_semantics env rho mul alpha enum top q x z).mp hx)
      ((relation_semantics env rho mul alpha enum top q y z).mp hy)
  exact ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top Y nalpha
    (relation rho mul alpha enum top) (Source.SetLanguage.args3 graph (env Y) (env nalpha)) 0 1 2
    hp hG hF ht hpre hY hNA (monotone env rho G F mul alpha enum top hpre)
    (congruent hM env rho G F mul alpha enum top hpre) (regular env rho G F mul alpha enum top hpre)
    hGraph rfl rfl htotal hone hinj hpW

/-- Pinned outside_uniformRange:282-311, specialized to the actual local list.
The constructed inverse graph discharges the no-injection contradiction. -/
theorem outside_localList (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y : Fin k) (p : M.Carrier .set)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (hHF : (Project.FirstOrderSemantics.reduct M).mem (env H) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hNames : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env H) (env names))
    (hAlpha : ForcingRawRank.Ordinal (env alpha))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo
      (KuratowskiZF.interpretation hM) (env enum) (env alpha) (env names))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env alpha) (env enum) (env (rho 6)) (env list))
    (hChecked : ForcingCheckName.Checked (env top) (env alpha) (env nalpha))
    (hY : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hfixY : ForcingSupportedNames.Supported (fun j => env (rho j)) (env H) (env Y))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hnot : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args1 (env Y)) (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env r q ∧
        ∃ x, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) r ∧
          ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) r x (env list) := by
  classical
  have htW := (hp.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have htop (q : M.Carrier .set) (_ : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6))) :
      MapRel (orderFormula (rho 0) mul) env q (env top) :=
    (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hchild : ∀ nu, ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env nu →
      ∀ chi c, PureKuratowski.PairMember M chi c nu →
        ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env chi := by
    intro nu hnu chi c he
    exact (ForcingPairUnion.domain_semantics env rho G F chi).mpr
      (ForcingHS.child ((ForcingPairUnion.domain_semantics env rho G F nu).mp hnu) he)
  have hNA := ForcingInfinity.check_hs hM (fun j => env (rho j)) hp hG hF ht hChecked
  have hNo := ForcingCheckOrdinal.no_check_injection_of_not_wellorderable hM hpre htW htop hchild
    hpW hnot hAlpha hChecked ((ForcingPairUnion.domain_semantics env rho G F (env nalpha)).mpr hNA)
  intro q hq hqp
  have hsub : ¬ (∀ x, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
      ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env r q →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) r →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env list) r) := by
    intro hsub
    obtain ⟨graph,_,hHS,_,hInject⟩ := construct hM env rho I K B w G F H mul top bound names alpha enum list nalpha Y q
      hp hG hF hH hHF ht hpre hNames hAlpha hEnum hList hChecked hY hfixY hq hsub
    exact hNo q hq hqp graph ((ForcingPairUnion.domain_semantics env rho G F graph).mpr hHS) hInject
  have hex : ∃ x, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x ∧
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env r q ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) r ∧
        ¬Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env list) r := by
    apply Classical.byContradiction
    intro hn
    apply hsub
    intro x hx r hr hrq hy
    exact Classical.byContradiction (fun hout => hn ⟨x,hx,r,hr,hrq,hy,hout⟩)
  obtain ⟨x,hx,r,hr,hrq,hy,hout⟩ := hex
  have hstrong : ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env s r ∧
      ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) s x (env list) := by
    apply Classical.byContradiction
    intro hn
    apply hout
    apply ForcingAtomicBasic.mem_of_dense hM hpre hr
    intro s hs hsr
    apply Classical.byContradiction
    intro hnone
    apply hn
    refine ⟨s,hs,hsr,?_⟩
    intro t htc hts hm
    exact hnone ⟨t,htc,hts,hm⟩
  obtain ⟨s,hs,hsr,hout⟩ := hstrong
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,x,hx,
    ForcingAtomicBasic.mem_mono hM hpre hs hsr hy,hout⟩

def subset {k : Nat} (rho : Fin 7 → Fin k) (G F mul p Y list : Fin k) : Formula k :=
  let up : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  .all ((ForcingHS.hs actionFormula (fun j => (rho j).castSucc) G.castSucc
    (rho 6).castSucc F.castSucc (Fin.last k)).imp
    (.all ((Formula.mem (Fin.last (k+1)) (up (rho 6))).imp
      ((ReplacementPredicates.rel (orderFormula (rho 0) mul) up (Fin.last (k+1)) (up p)).imp
        ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) up (up (rho 6))
          (Fin.last k).castSucc (up Y) (Fin.last (k+1))).imp
          (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) up (up (rho 6))
            (Fin.last k).castSucc (up list) (Fin.last (k+1))))))))

theorem subset_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul p Y list : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (subset rho G F mul p Y list) ↔
      ∀ x, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q (env p) →
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) q →
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env list) q := by
  simp only [subset,Formula.Realize,ForcingHS.hs_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionResult {k : Nat} (rho : Fin 7 → Fin k)
    (G F H mul top alpha enum nalpha Y p : Fin k) : Project.Formula 1 k :=
  .existsE ((ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul)
    (relation rho mul alpha enum top) Fin.succ (rho 6) top Y nalpha 0)).conj
    ((ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (rho j).succ)
      G.succ (rho 6).succ F.succ 0)).conj
    ((ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (rho j).succ) H.succ 0)).conj
      (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul)
        (ForcingPairUnion.domain rho G F) Fin.succ (Source.SetLanguage.args3 0 Y.succ nalpha.succ)
        (rho 6).succ p.succ (Source.SetLanguage.injection 0 1 2))))))

def premises {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k) :
    List (Project.Formula 1 k) :=
  [ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
   ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G H),
   .mem (.bound H) (.bound F),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
   ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound H names),
   ProjectSyntax.encode id (OrdinalSyntax.ordinal alpha),
   Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound alpha) (.bound names),
   ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 alpha enum (rho 6) list),
   ProjectSyntax.encode id (ForcingCheckName.checkName top alpha nalpha),
   ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
   ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho H Y),
   .mem (.bound p) (.bound (rho 6)),
   ProjectSyntax.encode id (subset rho G F mul p Y list)]

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ((premises rho I K B w G F H mul top bound names alpha enum list nalpha Y p).foldr
      (fun a b => .imp a b) (constructionResult rho G F H mul top alpha enum nalpha Y p))
  freeClosed := by
    simp -implicitDefEqProofs [premises,constructionResult,List.foldr,
      Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w G F H mul top bound names alpha enum list nalpha Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingLocalNames.carrier_semantics (M := M),ForcingRawRank.ordinal_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),subset_semantics (M := M)]
  intro hp hG hF hH hHF ht hpre hNames hAlpha hEnum hList hChecked hY hfixY hpW hsub
  obtain ⟨graph,hGraph,hHS,hFixed,hInject⟩ := construct hM env rho I K B w G F H mul top bound names alpha enum list nalpha Y (env p)
    hp hG hF hH hHF ht hpre hNames hAlpha hEnum hList hChecked hY hfixY hpW hsub
  simp only [constructionResult,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingRelationGraph.graph_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingFormula.formula_semantics (M := M)]
  exact ⟨graph,hGraph,hHS,hFixed,hInject⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (constructionSentence rho I K B w G F H mul top bound names alpha enum list nalpha Y p)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w G F H mul top bound names alpha enum list nalpha Y p hM)

def outsideResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul Y list p : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+1) := Fin.succ
  let up2 : Fin k → Fin (k+2) := fun j => j.succ.succ
  let up3 : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  .forallE ((Definitional.Formula.mem (.bound 0) (.bound (up (rho 6)))).imp
    ((ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) up 0 (up p))).imp
      (.existsE ((Definitional.Formula.mem (.bound 0) (.bound (up2 (rho 6)))).conj
        ((ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) up2 0 1)).conj
          (.existsE ((ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up3 (rho j))
            (up3 G) (up3 (rho 6)) (up3 F) 0)).conj
            ((ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul)
              up3 (up3 (rho 6)) 0 (up3 Y) 1)).conj
              (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul)
                up3 (up3 (rho 6)) 1 0 (up3 list)))))))))))

def outsideSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (((premises rho I K B w G F H mul top bound names alpha enum list nalpha Y p).take 15).foldr
      (fun a b => .imp a b)
      ((ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul)
        (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args1 Y) (rho 6) p
        (ForcingCheckOrdinal.wellorderable 0).neg)).imp (outsideResult rho G F mul Y list p)))
  freeClosed := by
    simp -implicitDefEqProofs [premises,outsideResult,List.take_succ_cons,List.take_zero,List.foldr,
      Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem outside_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (outsideSentence rho I K B w G F H mul top bound names alpha enum list nalpha Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [premises,List.take_succ_cons,List.take_zero,List.foldr,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingLocalNames.carrier_semantics (M := M),ForcingRawRank.ordinal_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),id_eq]
  intro hp hG hF hH hHF ht hpre hNames hAlpha hEnum hList hChecked hY hfixY hpW hnot
  have harg : (fun i => env (Source.SetLanguage.args1 Y i)) = Source.SetLanguage.args1 (env Y) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [harg] at hnot
  have hout := outside_localList hM env rho I K B w G F H mul top bound names alpha enum list nalpha Y (env p)
    hp hG hF hH hHF ht hpre hNames hAlpha hEnum hList hChecked hY hfixY hpW hnot
  simp only [outsideResult,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingOutsideLocal.outside_semantics (M := M)]
  exact hout

theorem outside_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F H mul top bound names alpha enum list nalpha Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (outsideSentence rho I K B w G F H mul top bound names alpha enum list nalpha Y p)) :=
  ModelTransfer.derives (fun _ hM => outside_models rho I K B w G F H mul top bound names alpha enum list nalpha Y p hM)

end PPAC.Migration.ForcingUniformInverseGraph
