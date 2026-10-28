/- Pinned AvailableRecords.le_of_common_and_range:196, intersection_le_root:208,
and eligibleSystem.intersection:281-289. Consume the existing actual quotient
intersection and eligibility reflection; return a member of the actual root Obj
with BOTH restricted Obj edges, not merely a class in the ambient quotient. -/
import PPAC.Migration.ForcingEligibleRestriction

namespace PPAC.Migration.ForcingEligibleIntersection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (Injection Small MapsTo)
open ForcingLocalAtomic (EqG)
open ForcingLocalQuotient (Classes Projection EqualityLaw)
open ForcingLocalRestriction (Restriction)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingAtomicRelations (Forces)
open ForcingSupportedNames (Range Supported)
open ForcingSupportingRoot (Code code_mem exists_code code_le restricted_condition)
open ConstructionCohenCompatibility (Restricted)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


theorem le_of_common_and_range (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e t r s : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (ht : Injection D I t) (hr : Injection D I r) (hs : Injection D I s)
    (htr : ForcingDiagramOrder.Le D mul t r) (hts : ForcingDiagramOrder.Le D mul t s)
    (hrs : ∀ z, ConstructionPlacementTriple.ImageAt s D z → ConstructionPlacementTriple.ImageAt r D z) :
    ForcingDiagramOrder.Le D mul r s := by
  obtain ⟨a,ha,hR⟩ := htr
  obtain ⟨b,hb,hS⟩ := hts
  obtain ⟨z,hbz,_⟩ := ht.1.1.2 b hb
  have hse := (hS e z).mpr ⟨hm.1.1,b,hb,((hm.1.2 b hb b).2).mpr rfl,hbz⟩
  obtain ⟨c,hc,hcz⟩ := hrs z ⟨e,hm.1.1,hse⟩
  obtain ⟨_,ac,_,hac,hacz⟩ := (hR c z).mp hcz
  have heq := ht.2 ac b z hacz hbz
  have hab : ForcingDiagramOrder.Product mul a c b := heq ▸ hac
  obtain ⟨u,hu,hU⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 c hc) hr
  have hTS := ForcingDiagramPoset.sub_sub hm ha hc hab hR hU
  have hus : u = s := ForcingDiagramPoset.injection_ext hM hu hs
    (fun x y => (hTS x y).trans (hS x y).symm)
  exact ⟨c,hc,hus ▸ hU⟩

theorem intersection_le_root (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e p s0 s1 q : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hs0 : Injection D I s0) (hp : Injection D I p) (hq : Injection D I q)
    (hs0p : ForcingDiagramOrder.Le D mul s0 p)
    (h0q : ForcingDiagramOrder.Le D mul s0 q) (h1q : ForcingDiagramOrder.Le D mul s1 q)
    (hInter : ConstructionDiagramPlacements.RangeIntersection D s0 s1 p) :
    ForcingDiagramOrder.Le D mul p q :=
  le_of_common_and_range hM hm hs0 hp hq hs0p h0q
    (fun z hz => (hInter z).mp ⟨ConstructionDescentPlacement.range_antitone h0q hz,
      ConstructionDescentPlacement.range_antitone h1q hz⟩)

theorem intersection (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g
      X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p) (hs0 : Injection (env (rho 0)) I s0)
    (hs1 : Injection (env (rho 0)) I s1) (hv : Injection (env (rho 0)) I v)
    (hs0p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s0 p)
    (hs1p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s1 p)
    (hInter : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) s0 s1 p)
    (hv0 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s0)
    (hv1 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s1)
    (hRange0 : Range (env (rho 0)) s0 A0) (hRange1 : Range (env (rho 0)) s1 A1)
    (hRangeP : Range (env (rho 0)) p Ap)
    (hFix0 : ForcingLabelPermutations.Fixing (env G) A0 fixing0)
    (hFix1 : ForcingLabelPermutations.Fixing (env G) A1 fixing1)
    (hFixP : ForcingLabelPermutations.Fixing (env G) Ap fixingP)

    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b nameBound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hX0 : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) nameBound fixing0 X0)
    (hX1 : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) nameBound fixing1 X1)
    (hXP : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) nameBound fixingP XP)
    (hpr0 : MapsTo X0 Q0 pr0) (hpr1 : MapsTo X1 Q1 pr1)
    (hQP : Classes (orderFormula (rho 0) mul) env (env (rho 6)) g p XP QP)
    (hPr0 : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g s0 X0 pr0)
    (hPr1 : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g s1 X1 pr1)
    (hPrP : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g p XP prP)
    (hPrv : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g v XV prv)
    (hF0 : Restriction pr0 prv f0) (hF1 : Restriction pr1 prv f1)
    (hK0 : Restriction prP pr0 k0) (hK1 : Restriction prP pr1 k1)
    (hq : Injection (env (rho 0)) I q)
    (hRangeQ : Range (env (rho 0)) q Aq)
    (hFixQ : ForcingLabelPermutations.Fixing (env G) Aq fixingQ)
    (hE : Supported (fun i => env (rho i)) fixingQ E)
    (hO0 : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g s0 q labels E pr0 Q0 O0)
    (hO1 : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g s1 q labels E pr1 Q1 O1)
    (hOP : ForcingEligibleObjects.Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g p q labels E prP QP OP)
    (hA0 : ForcingEligibleRestriction.Restricts a0 f0 O0) (hA1 : ForcingEligibleRestriction.Restricts a1 f1 O1)
    (hB0 : ForcingEligibleRestriction.Restricts b0 k0 OP) (hB1 : ForcingEligibleRestriction.Restricts b1 k1 OP)
    (hE0 : PureKuratowski.PairMember M x0 y a0) (hE1 : PureKuratowski.PairMember M x1 y a1) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x OP ∧
      PureKuratowski.PairMember M x x0 b0 ∧ PureKuratowski.PairMember M x x1 b1 := by
  obtain ⟨he0,hx0⟩ := (hA0 x0 y).mp hE0
  obtain ⟨he1,hx1⟩ := (hA1 x1 y).mp hE1
  obtain ⟨_,h0q,hel0⟩ := (hO0 x0).mp hx0
  obtain ⟨_,h1q,_⟩ := (hO1 x1).mp hx1
  have hpq := intersection_le_root hM hm hs0 hp hq hs0p h0q h1q hInter
  obtain ⟨x,hx,hk0,hk1⟩ := ForcingLocalIntersection.intersection hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1
    hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP
    hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 he0 he1
  have hAqP : ForcingPowerName.Subset Aq Ap := fun z hz =>
    (hRangeP z).mpr (ConstructionDescentPlacement.range_antitone hpq ((hRangeQ z).mp hz))
  have hEP := ForcingSupportedNames.supported_mono hFixQ hFixP hAqP hE
  have hel := (ForcingEligibilityReflection.eligible_restrict_iff hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs0p hRangeP hFixP hg
    hc ht hLabels hEP hXP hPrP hPr0 hK0 hk0).mp hel0
  have hxO := (hOP x).mpr ⟨hx,hpq,hel⟩
  exact ⟨x,hxO,(hB0 x x0).mpr ⟨hk0,hxO⟩,(hB1 x x1).mpr ⟨hk1,hxO⟩⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s0 (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s1 (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection v (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s0 p))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s1 p))
    (.imp (ConstructionDiagramPlacements.rangeIntersection (rho 0) s0 s1 p)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s0))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s1))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s0 A0))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s1 A1))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A0 fixing0))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A1 fixing1))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap fixingP))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b nameBound))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F nameBound fixing0 X0))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F nameBound fixing1 X1))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F nameBound fixingP XP))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr0 X0 Q0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr1 X1 Q1))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.classes (orderFormula (rho 0) mul) id (rho 6) g p XP QP))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g s0 X0 pr0))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g s1 X1 pr1))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g p XP prP))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g v XV prv))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction pr0 prv f0))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction pr1 prv f1))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction prP pr0 k0))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction prP pr1 k1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq fixingQ))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixingQ E))
    (.imp (ProjectSyntax.encode id (ForcingEligibleObjects.carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g s0 q labels E pr0 Q0 O0))
    (.imp (ProjectSyntax.encode id (ForcingEligibleObjects.carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g s1 q labels E pr1 Q1 O1))
    (.imp (ProjectSyntax.encode id (ForcingEligibleObjects.carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g p q labels E prP QP OP))
    (.imp (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw a0 f0 O0))
    (.imp (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw a1 f1 O1))
    (.imp (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw b0 k0 OP))
    (.imp (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw b1 k1 OP))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge a0 x0 y))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge a1 x1 y))
    (ProjectSyntax.encode id (ForcingLocalIntersection.result OP b0 b1 x0 x1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,
      ConstructionDiagramPlacements.rangeIntersection_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.le_semantics (M := M),
    ConstructionDiagramPlacements.rangeIntersection_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingLocalNames.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLocalQuotient.classes_semantics (M := M),
    ForcingLocalQuotient.projection_semantics (M := M),
    ForcingLocalRestriction.restriction_semantics (M := M),
    KuratowskiZF.source_edge (M := M),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLocalIntersection.result_semantics (M := M),
    ForcingEligibleObjects.carrier_semantics (M := M),
    ForcingEligibleRestriction.edgeLaw_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),
    Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hq hRangeQ hFixQ hE hO0 hO1 hOP hA0 hA1 hB0 hB1 hE0 hE1
  exact intersection hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hq hRangeQ hFixQ hE hO0 hO1 hOP hA0 hA1 hB0 hB1 hE0 hE1

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let zero := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => zero }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 hL hChoice)


end PPAC.Migration.ForcingEligibleIntersection
