/- Pinned LocalQuotient.intersection:536-554. Consume the actual local-name
support descent and the constructed projections and restrictions at the same roots. -/
import PPAC.Migration.ForcingLocalInjectivity

namespace PPAC.Migration.ForcingLocalIntersection
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


theorem intersection (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g
      X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y : M.Carrier .set}
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
    (hE0 : PureKuratowski.PairMember M x0 y f0) (hE1 : PureKuratowski.PairMember M x1 y f1) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x QP ∧
      PureKuratowski.PairMember M x x0 k0 ∧ PureKuratowski.PairMember M x x1 k1 := by
  obtain ⟨sigma0,hs0x,hs0y⟩ := (hF0 x0 y).mp hE0
  obtain ⟨sigma1,hs1x,hs1y⟩ := (hF1 x1 y).mp hE1
  have hn0 := (hX0 sigma0).mp ((hPr0 sigma0 x0).mp hs0x).1
  have hn1 := (hX1 sigma1).mp ((hPr1 sigma1 x1).mp hs1x).1
  have he := (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hv hPrv
    sigma0 sigma1 y y hs0y hs1y).mp rfl
  obtain ⟨d,z,hdg,hz,heq⟩ := he
  have hd := (hpres.2.2.1 d).mp (hg.1 d hdg)
  obtain ⟨d0,hd0,hRestr0,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A0
  obtain ⟨d1,hd1,hRestr1,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A1
  obtain ⟨z0,hz0⟩ := exists_code hM d0 s0
  obtain ⟨z1,hz1⟩ := exists_code hM d1 s1
  obtain ⟨sigma,hn,he0,he1⟩ := ForcingLocalNameDescent.localName_descent hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1
    hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hn0 hn1 hd hRestr0 hRestr1 hz hz0 hz1 heq
    hc ht hLabels hBound
  have hSigmaP := (hXP sigma).mpr hn
  obtain ⟨x,hClass⟩ := ForcingLocalQuotient.exists_class hM (orderFormula (rho 0) mul) env
    (env (rho 6)) g p XP sigma
  have hxQP := (hQP x).mpr ⟨sigma,hSigmaP,hClass⟩
  have hSigmaX := (hPrP sigma x).mpr ⟨hSigmaP,hClass⟩
  have hAp0 : ForcingPowerName.Subset Ap A0 := fun j hj =>
    (hRange0 j).mpr (ConstructionDescentPlacement.range_antitone hs0p ((hRangeP j).mp hj))
  have hAp1 : ForcingPowerName.Subset Ap A1 := fun j hj =>
    (hRange1 j).mpr (ConstructionDescentPlacement.range_antitone hs1p ((hRangeP j).mp hj))
  have hSigma0 := ForcingLocalNames.restrict_name hFixP hFix0 hAp0 hXP hX0 sigma hSigmaP
  have hSigma1 := ForcingLocalNames.restrict_name hFixP hFix1 hAp1 hXP hX1 sigma hSigmaP
  obtain ⟨x0',hsx0,_⟩ := hpr0.1.2 sigma hSigma0
  obtain ⟨x1',hsx1,_⟩ := hpr1.1.2 sigma hSigma1
  have hd0g := hg.2.2.1 d d0 hdg ((hpres.2.2.1 d0).mpr hd0)
    (fun t ht => ((hRestr0 t).mp ht).1)
  have hd1g := hg.2.2.1 d d1 hdg ((hpres.2.2.1 d1).mpr hd1)
    (fun t ht => ((hRestr1 t).mp ht).1)
  have hEq0 := (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hs0 hPr0
    sigma sigma0 x0' x0 hsx0 hs0x).mpr ⟨d0,z0,hd0g,hz0,he0⟩
  have hEq1 := (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hs1 hPr1
    sigma sigma1 x1' x1 hsx1 hs1x).mpr ⟨d1,z1,hd1g,hz1,he1⟩
  exact ⟨x,hxQP,ForcingLocalRestriction.restrict_ofName hK0 hSigmaX (hEq0 ▸ hsx0),
    ForcingLocalRestriction.restrict_ofName hK1 hSigmaX (hEq1 ▸ hsx1)⟩

def result {k : Nat} (QP k0 k1 x0 x1 : Fin k) : Formula k :=
  .ex ((Formula.mem (Fin.last k) QP.castSucc).conj
    ((Source.SetLanguage.edge k0.castSucc (Fin.last k) x0.castSucc).conj
      (Source.SetLanguage.edge k1.castSucc (Fin.last k) x1.castSucc)))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (QP k0 k1 x0 x1 : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result QP k0 k1 x0 x1) ↔
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x (env QP) ∧
      PureKuratowski.PairMember M x (env x0) (env k0) ∧
      PureKuratowski.PairMember M x (env x1) (env k1) := by
  simp only [result,Formula.Realize,KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]


def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y : Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f0 x0 y))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f1 x1 y))
    (ProjectSyntax.encode id (result QP k0 k1 x0 x1))))))))))))))))))))))))))))))))))))))))))))))))
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
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y)]
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
    result_semantics (M := M),
    Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hE0 hE1
  exact intersection hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hE0 hE1

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y hL hChoice)


end PPAC.Migration.ForcingLocalIntersection
