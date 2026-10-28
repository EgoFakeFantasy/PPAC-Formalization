/- Pinned AvailableRecords.eligibleSystem:275-279. Discharge quotient-law
premises using the actual LocalQuotient producers. No identity, composition
or injection law is assumed as an input; carriers, projections and the exact
constructed restriction graphs remain explicit for indexed assembly. -/
import PPAC.Migration.ForcingEligibleIntersection

namespace PPAC.Migration.ForcingEligibleLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (Injection Small MapsTo)
open ForcingLocalAtomic (EqG)
open ForcingLocalQuotient (Projection EqualityLaw)
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

def identitySentence {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Q pr f V a : Fin k) : Source.Sentence :=
  ((Source.SetLanguage.mapsTo pr X Q).imp ((ForcingLocalQuotient.classes R id W g r X Q).imp ((ForcingLocalQuotient.projection R id W g r X pr).imp ((ForcingLocalRestriction.restriction pr pr f).imp ((ForcingEligibleObjects.carrier R Hdom id D mul W g r q labels E pr Q V).imp ((RestrictionSyntax.edgeLaw a f V).imp (ForcingConditionGraphs.identityGraph V a))))))).close

theorem identity_models {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Q pr f V a : Fin k)
    (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (identitySentence R Hdom D mul W g r q labels E X Q pr f V a)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpr hQ hPr hf hV ha
  have hpr := (ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr
  have hQ := (ForcingLocalQuotient.classes_semantics (M := M) env R id W g r X Q).mp hQ
  have hPr := (ForcingLocalQuotient.projection_semantics (M := M) env R id W g r X pr).mp hPr
  have hf := (ForcingLocalRestriction.restriction_semantics (M := M) env pr pr f).mp hf
  have hV := (ForcingEligibleObjects.carrier_semantics (M := M) env R Hdom id D mul W g r q labels E pr Q V).mp hV
  have ha := (ForcingEligibleRestriction.edgeLaw_semantics (M := M) env a f V).mp ha
  apply (ForcingConditionGraphs.identityGraph_semantics (M := M) env V a).mpr
  exact ForcingEligibleRestriction.restrict_refl
    (ForcingLocalRestriction.restrict_refl hpr hQ hPr hf)
    (fun x hx => ((hV x).mp hx).1) ha

theorem identity_kernel_certificate {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Q pr f V a : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (identitySentence R Hdom D mul W g r q labels E X Q pr f V a)) :=
  ModelTransfer.derives (fun _ hM => identity_models R Hdom D mul W g r q labels E X Q pr f V a hM)

def compositionSentence {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02 : Fin k) : Source.Sentence :=
  ((Source.SetLanguage.subset X Y).imp ((Source.SetLanguage.subset Y Z).imp ((Source.SetLanguage.mapsTo pr X Q).imp ((Source.SetLanguage.mapsTo ps Y T).imp ((Source.SetLanguage.mapsTo pt Z U).imp ((Source.SetLanguage.mapsTo f12 T U).imp ((ForcingLocalRestriction.restriction pr ps f01).imp ((ForcingLocalRestriction.restriction ps pt f12).imp ((ForcingLocalRestriction.restriction pr pt f02).imp ((ForcingEligibleObjects.carrier R Hdom id D mul W g r q labels E pr Q V).imp ((RestrictionSyntax.edgeLaw a01 f01 V).imp ((RestrictionSyntax.edgeLaw a12 f12 J).imp ((RestrictionSyntax.edgeLaw a02 f02 V).imp ((Source.SetLanguage.mapsTo a01 V J).imp (ForcingConditionGraphs.compositionGraph V a12 a01 a02))))))))))))))).close

theorem composition_models {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02 : Fin k)
    (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (compositionSentence R Hdom D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hXY hYZ hpr hps hpt hf12 h01 h12 h02 hV ha01 ha12 ha02 hMap
  have hXY := (ForcingLabelPermutations.subset_semantics (M := M) env X Y).mp hXY
  have hYZ := (ForcingLabelPermutations.subset_semantics (M := M) env Y Z).mp hYZ
  have hpr := (ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr
  have hps := (ForcingSupportSize.mapsTo_semantics (M := M) env ps Y T).mp hps
  have hpt := (ForcingSupportSize.mapsTo_semantics (M := M) env pt Z U).mp hpt
  have hf12 := (ForcingSupportSize.mapsTo_semantics (M := M) env f12 T U).mp hf12
  have h01 := (ForcingLocalRestriction.restriction_semantics (M := M) env pr ps f01).mp h01
  have h12 := (ForcingLocalRestriction.restriction_semantics (M := M) env ps pt f12).mp h12
  have h02 := (ForcingLocalRestriction.restriction_semantics (M := M) env pr pt f02).mp h02
  have hV := (ForcingEligibleObjects.carrier_semantics (M := M) env R Hdom id D mul W g r q labels E pr Q V).mp hV
  have ha01 := (ForcingEligibleRestriction.edgeLaw_semantics (M := M) env a01 f01 V).mp ha01
  have ha12 := (ForcingEligibleRestriction.edgeLaw_semantics (M := M) env a12 f12 J).mp ha12
  have ha02 := (ForcingEligibleRestriction.edgeLaw_semantics (M := M) env a02 f02 V).mp ha02
  have hMap := (ForcingSupportSize.mapsTo_semantics (M := M) env a01 V J).mp hMap
  apply (ForcingConditionGraphs.compositionGraph_semantics (M := M) env V a12 a01 a02).mpr
  exact ForcingEligibleRestriction.restrict_comp
    (ForcingLocalRestriction.restrict_restrict hXY hYZ hpr hps hpt hf12 h01 h12 h02)
    (fun x hx => ((hV x).mp hx).1) ha01 ha12 ha02 hMap

theorem composition_kernel_certificate {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02 : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (compositionSentence R Hdom D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02)) :=
  ModelTransfer.derives (fun _ hM => composition_models R Hdom D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02 hM)

theorem restrict_injective (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s g A fixing nameBound X Y Q T pr ps f V J a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))

    (hp : Injection (env (rho 0)) I p) (hs : Injection (env (rho 0)) I s)
    (hsp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s p)
    (hRange : Range (env (rho 0)) p A)
    (hFix : ForcingLabelPermutations.Fixing (env G) A fixing)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hX : ForcingLocalNames.Carrier (fun i => env (rho i)) (env G) (env F) nameBound fixing X)
    (hPr : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g p X pr)
    (hPs : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g s Y ps)
    (hf : MapsTo Q T f) (hRestr : Restriction pr ps f)
    (hA : ForcingEligibleRestriction.Restricts a f V) (hMap : MapsTo V J a) : Injection V J a := by
  exact ForcingEligibleRestriction.restrict_injective
    (ForcingLocalInjectivity.restrict_injective hM hChoice env rho G F mul
      hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hRange hFix hg hX hPr hPs hf hRestr)
    hA hMap

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a : Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s p))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A fixing))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F nameBound fixing X))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g p X pr))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g s Y ps))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f Q T))
    (.imp (ProjectSyntax.encode id (ForcingLocalRestriction.restriction pr ps f))
    (.imp (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw a f V))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo a V J))
    (ProjectSyntax.encode id (Source.SetLanguage.injection a V J)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a)]
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
    ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingLocalNames.carrier_semantics (M := M),
    ForcingLocalQuotient.projection_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLocalRestriction.restriction_semantics (M := M),
    ForcingEligibleRestriction.edgeLaw_semantics (M := M),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hRange hFix hg hX hPr hPs hf hRestr hA hMap
  exact restrict_injective hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hRange hFix hg hX hPr hPs hf hRestr hA hMap

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a hL hChoice)


end PPAC.Migration.ForcingEligibleLaws
