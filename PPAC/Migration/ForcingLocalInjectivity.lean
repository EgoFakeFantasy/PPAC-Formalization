/- Pinned LocalQuotient.restrict_injective:511-532. Reflect EqG to the
original supporting root using the existing Cohen restriction and root theorem. -/
import PPAC.Migration.ForcingLocalRestriction

namespace PPAC.Migration.ForcingLocalInjectivity
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

theorem eqG_reflect (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s g A fixing sigma tau : M.Carrier .set}
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
    (hSigma : Supported (fun i => env (rho i)) fixing sigma)
    (hTau : Supported (fun i => env (rho i)) fixing tau)
    (he : EqG (orderFormula (rho 0) mul) env (env (rho 6)) g s sigma tau) :
    EqG (orderFormula (rho 0) mul) env (env (rho 6)) g p sigma tau := by
  obtain ⟨d,z,hdg,hz,heq⟩ := he
  have hd := (hpres.2.2.1 d).mp (hg.1 d hdg)
  obtain ⟨dR,hdR,hR,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A
  obtain ⟨zR,hzR⟩ := exists_code hM dR p
  have hdRg := hg.2.2.1 d dR hdg ((hpres.2.2.1 dR).mpr hdR)
    (fun t ht => ((hR t).mp ht).1)
  have hsup : ∀ j : Fin 2, Supported (fun i => env (rho i)) fixing (args2 sigma tau j) := by
    intro j
    exact Fin.cases hSigma (fun j => Fin.cases hTau (fun j => Fin.elim0 j) j) j
  have heR : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma tau zR :=
    ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul
      hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hd hRange hFix hR hz hzR
      (.equal (0 : Fin 2) 1) (args2 sigma tau) hsup heq
  exact ⟨dR,zR,hdRg,hzR,heR⟩

theorem restrict_injective (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s g A fixing nameBound X Y Q T pr ps f : M.Carrier .set}
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
    (hf : MapsTo Q T f) (hRestr : Restriction pr ps f) : Injection Q T f := by
  refine ⟨hf,?_⟩
  intro x y z hx hy
  obtain ⟨sigma,hsc,hsz⟩ := (hRestr x z).mp hx
  obtain ⟨tau,htc,htz⟩ := (hRestr y z).mp hy
  have hnSigma := (hX sigma).mp ((hPr sigma x).mp hsc).1
  have hnTau := (hX tau).mp ((hPr tau y).mp htc).1
  have he := (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hs hPs
    sigma tau z z hsz htz).mp rfl
  have heR := eqG_reflect hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
    hpres hG hFilter hp hs hsp hRange hFix hg hnSigma.2 hnTau.2 he
  exact (ForcingLocalQuotient.equality_law hM env rho mul hm hpres hg hp hPr
    sigma tau x y hsc htc).mpr heR


def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f : Fin k) : Project.Sentence where
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
    (ProjectSyntax.encode id (Source.SetLanguage.injection f Q T)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f)]
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
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hRange hFix hg hX hPr hPs hf hRestr
  exact restrict_injective hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs hsp hRange hFix hg hX hPr hPs hf hRestr

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f hL hChoice)


end PPAC.Migration.ForcingLocalInjectivity
