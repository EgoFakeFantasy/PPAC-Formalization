/- Pinned AvailableRecords.eligibleSystem:273-279. Restrict the already
constructed quotient map to the actual eligible Obj sets. The native
restriction constructor and existing edgeLaw formula are reused. The three
map laws consume the already proved quotient laws; full system/intersection
and indexed assembly remain separate consumers. -/
import PPAC.Migration.ForcingEligibleObjects
import PPAC.Migration.ObjectRestriction

namespace PPAC.Migration.ForcingEligibleRestriction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (IdentityGraph CompositionGraph)
open ForcingEligibleObjects (Carrier carrier)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Semantic view of the already existing RestrictionSyntax.edgeLaw. -/
def Restricts (a f V : M.Carrier .set) : Prop :=
  ∀ x y, PureKuratowski.PairMember M x y a ↔
    PureKuratowski.PairMember M x y f ∧ (Project.FirstOrderSemantics.reduct M).mem x V

theorem edgeLaw_semantics {k : Nat} (env : Fin k → M.Carrier .set) (a f V : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (RestrictionSyntax.edgeLaw a f V) ↔
      Restricts (env a) (env f) (env V) := by
  simp only [RestrictionSyntax.edgeLaw,Restricts,← GraphSyntax.edge_original,Source.Formula.iff,Formula.Realize,
    KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x y => ⟨(h x y).1,(h x y).2⟩,fun h x y => ⟨(h x y).mp,(h x y).mpr⟩⟩

theorem exists_restriction (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g r s q labels E X pr ps Q T V U f : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : Injection (env (rho 0)) I r) (hs : Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (hPr : ForcingLocalQuotient.Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hf : MapsTo Q T f) (hR : ForcingLocalRestriction.Restriction pr ps f)
    (hV : Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g r q labels E pr Q V)
    (hU : Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) g s q labels E ps T U) :
    ∃ a, MapsTo V U a ∧ Restricts a f V := by
  obtain ⟨a,ha⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) f V
  have he : Restricts a f V := fun x y => (ha.2 x y).trans and_comm
  refine ⟨a,⟨⟨?_,?_⟩,?_⟩,he⟩
  · intro row hrow
    obtain ⟨x,y,hcode⟩ := ha.1 row hrow
    exact ⟨x,y,((ha.2 x y).mp ⟨row,hcode,hrow⟩).1,hcode⟩
  · intro x hx
    obtain ⟨y,hxy,_⟩ := hf.1.2 x ((hV x).mp hx).1
    exact ⟨y,(he x y).mpr ⟨hxy,hx⟩,
      fun z hz => ForcingConditionGraphs.function_unique hf.1 ((he x z).mp hz).1 hxy⟩
  · intro x y hxy
    obtain ⟨hxy,hx⟩ := (he x y).mp hxy
    obtain ⟨_,hrq,hel⟩ := (hV x).mp hx
    exact (hU y).mpr ⟨hf.2 x y hxy,ForcingDiagramPoset.le_trans hm hsr hrq,
      ForcingEligibility.eligible_restrict hM env rho G F mul hm hp hg hr hs hsr hPr hR hxy hel⟩

theorem restrict_refl {Q V f a : M.Carrier .set}
    (hf : IdentityGraph Q f) (hV : ForcingPowerName.Subset V Q)
    (ha : Restricts a f V) : IdentityGraph V a := by
  intro x y
  constructor
  · intro h
    obtain ⟨he,hx⟩ := (ha x y).mp h
    exact ⟨hx,((hf x y).mp he).2⟩
  · rintro ⟨hx,rfl⟩
    exact (ha x x).mpr ⟨(hf x x).mpr ⟨hV x hx,rfl⟩,hx⟩

theorem restrict_comp {Q V U f g h a b c : M.Carrier .set}
    (hh : CompositionGraph Q g f h) (hV : ForcingPowerName.Subset V Q)
    (ha : Restricts a f V) (hb : Restricts b g U) (hc : Restricts c h V)
    (hMap : MapsTo V U a) : CompositionGraph V b a c := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hxz,hx⟩ := (hc x z).mp hxz
    obtain ⟨_,y,hxy,hyz⟩ := (hh x z).mp hxz
    have haxy := (ha x y).mpr ⟨hxy,hx⟩
    exact ⟨hx,y,haxy,(hb y z).mpr ⟨hyz,hMap.2 x y haxy⟩⟩
  · rintro ⟨hx,y,hxy,hyz⟩
    exact (hc x z).mpr ⟨(hh x z).mpr ⟨hV x hx,y,((ha x y).mp hxy).1,((hb y z).mp hyz).1⟩,hx⟩

theorem restrict_injective {Q T V U f a : M.Carrier .set}
    (hf : Injection Q T f) (ha : Restricts a f V) (hMap : MapsTo V U a) : Injection V U a :=
  ⟨hMap,fun x y z hx hy => hf.2 x y z ((ha x z).mp hx).1 ((ha y z).mp hy).1⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s q labels E X pr ps Q T V U f : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp ((Source.SetLanguage.injection r (rho 0) I).imp ((Source.SetLanguage.injection s (rho 0) I).imp ((ForcingDiagramOrder.le (rho 0) mul s r).imp ((ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g r X pr).imp ((Source.SetLanguage.mapsTo f Q T).imp ((ForcingLocalRestriction.restriction pr ps f).imp ((carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g r q labels E pr Q V).imp ((carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g s q labels E ps T U).imp (Formula.ex ((Source.SetLanguage.mapsTo (Fin.last k) V.castSucc U.castSucc).conj (RestrictionSyntax.edgeLaw (Fin.last k) f.castSucc V.castSucc)))))))))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s q labels E X pr ps Q T V U f : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w e G F mul g r s q labels E X pr ps Q T V U f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg hr hs hsr hPr hf hR hV hU
  obtain ⟨a,ha,he⟩ := exists_restriction hM env rho G F mul
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingSupportSize.injection_semantics (M := M) env s (rho 0) I).mp hs)
    ((ForcingDiagramOrder.le_semantics (M := M) env (rho 0) mul s r).mp hsr)
    ((ForcingLocalQuotient.projection_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g r X pr).mp hPr)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env f Q T).mp hf)
    ((ForcingLocalRestriction.restriction_semantics (M := M) env pr ps f).mp hR)
    ((ForcingEligibleObjects.carrier_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g r q labels E pr Q V).mp hV)
    ((ForcingEligibleObjects.carrier_semantics (M := M) env (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 0) mul (rho 6) g s q labels E ps T U).mp hU)
  refine ⟨a,?_,?_⟩
  · apply (ForcingSupportSize.mapsTo_semantics (M := M) (Fin.lastCases a env)
      (Fin.last k) V.castSucc U.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using ha
  · apply (edgeLaw_semantics (M := M) (Fin.lastCases a env)
      (Fin.last k) f.castSucc V.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using he

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s q labels E X pr ps Q T V U f : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w e G F mul g r s q labels E X pr ps Q T V U f)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w e G F mul g r s q labels E X pr ps Q T V U f hM)

def identitySentence : Source.Sentence :=
  (((ForcingConditionGraphs.identityGraph 0 2).imp ((Source.SetLanguage.subset 1 0).imp ((RestrictionSyntax.edgeLaw 3 2 1).imp (ForcingConditionGraphs.identityGraph 1 3)))) : Formula 4).close

theorem identity_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf hV ha
  apply (ForcingConditionGraphs.identityGraph_semantics (M := M) env 1 3).mpr
  exact restrict_refl
    ((ForcingConditionGraphs.identityGraph_semantics (M := M) env 0 2).mp hf)
    ((ForcingLabelPermutations.subset_semantics (M := M) env 1 0).mp hV)
    ((edgeLaw_semantics (M := M) env 3 2 1).mp ha)

theorem identity_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)

def compositionSentence : Source.Sentence :=
  (((ForcingConditionGraphs.compositionGraph 0 4 3 5).imp ((Source.SetLanguage.subset 1 0).imp ((RestrictionSyntax.edgeLaw 6 3 1).imp ((RestrictionSyntax.edgeLaw 7 4 2).imp ((RestrictionSyntax.edgeLaw 8 5 1).imp ((Source.SetLanguage.mapsTo 6 1 2).imp (ForcingConditionGraphs.compositionGraph 1 7 6 8))))))) : Formula 9).close

theorem composition_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence compositionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hh hV ha hb hc hMap
  apply (ForcingConditionGraphs.compositionGraph_semantics (M := M) env 1 7 6 8).mpr
  exact restrict_comp
    ((ForcingConditionGraphs.compositionGraph_semantics (M := M) env 0 4 3 5).mp hh)
    ((ForcingLabelPermutations.subset_semantics (M := M) env 1 0).mp hV)
    ((edgeLaw_semantics (M := M) env 6 3 1).mp ha)
    ((edgeLaw_semantics (M := M) env 7 4 2).mp hb)
    ((edgeLaw_semantics (M := M) env 8 5 1).mp hc)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env 6 1 2).mp hMap)

theorem composition_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence compositionSentence) :=
  ModelTransfer.derives (fun _ hM => composition_models hM)

def injectivitySentence : Source.Sentence :=
  (((Source.SetLanguage.injection 4 0 1).imp ((RestrictionSyntax.edgeLaw 5 4 2).imp ((Source.SetLanguage.mapsTo 5 2 3).imp (Source.SetLanguage.injection 5 2 3)))) : Formula 6).close

theorem injectivity_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence injectivitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf ha hMap
  apply (ForcingSupportSize.injection_semantics (M := M) env 5 2 3).mpr
  exact restrict_injective
    ((ForcingSupportSize.injection_semantics (M := M) env 4 0 1).mp hf)
    ((edgeLaw_semantics (M := M) env 5 4 2).mp ha)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env 5 2 3).mp hMap)

theorem injectivity_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence injectivitySentence) :=
  ModelTransfer.derives (fun _ hM => injectivity_models hM)

end PPAC.Migration.ForcingEligibleRestriction
