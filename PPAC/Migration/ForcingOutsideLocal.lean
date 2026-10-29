/- Pinned ClassFibers.OutsideLocal / outsideLocal_not_image.
Persistent exclusion is quantified over all actual stronger Product conditions;
the conclusion concerns the existing literal quotient restriction graph. -/
import PPAC.Migration.ForcingLocalList
import PPAC.Migration.ForcingLocalIntersection

namespace PPAC.Migration.ForcingOutsideLocal
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingSupportingRoot (Code exists_code code_mem code_le)
open ForcingPowerName (trueTest)
open ForcingSupportSize (Injection Small MapsTo)
open ForcingProductFamily (Presentation)
open ForcingSupportedNames (Range)
open ForcingLocalQuotient (Classes Projection)
open ForcingLocalRestriction (Restriction)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Outside {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W z sigma list : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q z →
    ¬ Forces false R env W sigma list q

def outside {k n : Nat} (R : Formula (k+2)) (base : Fin k → Fin n)
    (W z sigma list : Fin n) : Formula n :=
  .all ((Formula.mem (Fin.last n) W.castSucc).imp
    ((ReplacementPredicates.rel R (fun i => (base i).castSucc) (Fin.last n) z.castSucc).imp
      ((ForcingAtomicRelations.forces false R (fun i => (base i).castSucc) W.castSucc sigma.castSucc list.castSucc (Fin.last n)).imp .bot)))

theorem outside_semantics {k n : Nat} (env : Fin n → M.Carrier .set)
    (R : Formula (k+2)) (base : Fin k → Fin n) (W z sigma list : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (outside R base W z sigma list) ↔
      Outside R (fun i => env (base i)) (env W) (env z) (env sigma) (env list) := by
  simp only [outside,Outside,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Filter directedness and full-list membership exclude actual EqG witnesses. -/
theorem not_eqG (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e G F bound H X ordinal enum list g s d z sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d g) (hz : Code z d s)
    (hX : ForcingLocalNames.Carrier (fun j => env (rho j)) G F bound H X)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hTau : ForcingLocalNames.LocalName (fun j => env (rho j)) G F bound H tau)
    (hout : Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list) :
    ¬ ForcingLocalAtomic.EqG (orderFormula (rho 0) mul) env (env (rho 6)) g s tau sigma := by
  rintro ⟨a,za,ha,hza,heq⟩
  obtain ⟨b,hb,hbd,hba⟩ := hg.2.2.2 d a hd ha
  obtain ⟨zb,hzb⟩ := exists_code hM b s
  have hbW := code_mem hp ((hp.2.2.1 b).mp (hg.1 b hb)) hs hzb
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hsrefl := ForcingDiagramPoset.le_refl hm hs
  have hbza := (orderFormula_semantics env (rho 0) mul zb za).mpr ((code_le hzb hza).mpr ⟨hba,hsrefl⟩)
  have hbz := (orderFormula_semantics env (rho 0) mul zb z).mpr ((code_le hzb hz).mpr ⟨hbd,hsrefl⟩)
  have hEq := ForcingAtomicBasic.eq_mono hM hpre hbW hbza heq
  have hMem := ForcingLocalList.localName_mem_localList hM (orderFormula (rho 0) mul) env (fun j => env (rho j)) hpre hX hEnum hList hbW hTau
  exact hout zb hbW hbz ((ForcingAtomicLaws.mem_congr_left hM hpre hEq).mp hMem)

theorem outsideLocal_not_image (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d g) (hz : Code z d s)
    (hX : ForcingLocalNames.Carrier (fun j => env (rho j)) G F bound H X)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hPrP : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g p X prP)
    (hPrS : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g s XS prS)
    (hf : ForcingLocalRestriction.Restriction prP prS f)
    (hSigma : PureKuratowski.PairMember M sigma y prS)
    (hout : Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list) :
    ¬ PureKuratowski.PairMember M x y f := by
  intro hxy
  obtain ⟨tau,htx,hty⟩ := (hf x y).mp hxy
  have hTau := (hX tau).mp ((hPrP tau x).mp htx).1
  have he := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hs hPrS tau sigma y y hty hSigma).mp rfl
  exact not_eqG hM env rho mul hm hp hg hs hd hz hX hEnum hList hTau hout he

def notImageSentence {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (.mem (.bound d) (.bound g))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound H X))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound X))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g p X prP))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g s XS prS))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction prP prS f))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge prS sigma y))
    (.imp (ProjectSyntax.encode id (outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
      (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge f x y)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem notImage_models {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (notImageSentence rho mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingLocalNames.carrier_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingLocalQuotient.projection_semantics (M := M),
    ForcingLocalRestriction.restriction_semantics (M := M),KuratowskiZF.source_edge,outside_semantics (M := M)]
  intro hm hp hg hs hd hz hX hEnum hList hPrP hPrS hf hSigma hout
  exact outsideLocal_not_image hM env rho mul hm hp hg hs hd hz hX hEnum hList hPrP hPrS hf hSigma hout

theorem notImage_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (notImageSentence rho mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y)) :=
  ModelTransfer.derives (fun _ hM => notImage_models rho mul I K B w e G F bound H X XS ordinal enum list g p s d z sigma prP prS f x y hM)

/-- Pinned outsideLocal_not_equal: consume the existing exact-intersection
support descent, then exclude its actual root preimage. -/
theorem outsideLocal_not_equal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g
      X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma : M.Carrier .set}
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
    (hE0 : PureKuratowski.PairMember M x0 y f0) (hE1 : PureKuratowski.PairMember M x1 y f1)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal XP)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d g) (hz : Code z d s0)
    (hSigma : PureKuratowski.PairMember M sigma x0 pr0)
    (hout : Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list) : False := by
  obtain ⟨x,_,hx,_⟩ := ForcingLocalIntersection.intersection hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1
    hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP
    hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hE0 hE1
  exact outsideLocal_not_image hM env rho mul hm hpres hg hs0 hd hz hXP hEnum hList hPrP hPr0 hK0 hSigma hout hx

def notEqualSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma : Fin k) : Project.Sentence where
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
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (.mem (.bound d) (.bound g))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr0 sigma x0))
    (.imp (ProjectSyntax.encode id (outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
    .falsum))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,
      ConstructionDiagramPlacements.rangeIntersection_freeClosed]

theorem notEqual_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (notEqualSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (notEqualSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma)]
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
    Project.Formula.satisfies_falsum_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),outside_semantics (M := M),
    Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hE0 hE1 hEnum hList hd hz hSigma hout
  exact outsideLocal_not_equal hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hE0 hE1 hEnum hList hd hz hSigma hout

theorem notEqual_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (notEqualSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma))) := by
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
  apply ConstructibleGround.relative_models hM (notEqualSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (notEqualSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma)).mp
      (notEqual_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y ordinal enum list d z sigma hL hChoice)


end PPAC.Migration.ForcingOutsideLocal
