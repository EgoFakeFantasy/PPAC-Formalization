/- Pinned LocalQuotients.LocalQuotient.restrict:485, restrict_ofName:494,
restrict_refl:498 and restrict_restrict:503. Descend by the exact same
representative through the native function constructor, without choosing one. -/
import PPAC.Migration.ForcingLocalQuotient

namespace PPAC.Migration.ForcingLocalRestriction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (MapsTo)
open ForcingPowerName (Subset)
open ForcingLocalQuotient (Classes Projection EqualityLaw)
open ForcingLocalAtomic (EqG)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ImageClass (pr ps c d : M.Carrier .set) : Prop :=
  ∃ sigma, PureKuratowski.PairMember M sigma c pr ∧ PureKuratowski.PairMember M sigma d ps

def imageClass {k : Nat} (pr ps c d : Fin k) : Formula k :=
  .ex ((Source.SetLanguage.edge pr.castSucc (Fin.last k) c.castSucc).conj
    (Source.SetLanguage.edge ps.castSucc (Fin.last k) d.castSucc))

theorem imageClass_semantics {k : Nat} (env : Fin k → M.Carrier .set) (pr ps c d : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (imageClass pr ps c d) ↔
      ImageClass (env pr) (env ps) (env c) (env d) := by
  simp only [imageClass,ImageClass,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Restriction (pr ps f : M.Carrier .set) : Prop :=
  ∀ c d, PureKuratowski.PairMember M c d f ↔ ImageClass pr ps c d

def restriction {k : Nat} (pr ps f : Fin k) : Formula k :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).iff
    (imageClass pr.castSucc.castSucc ps.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1)))))

theorem restriction_semantics {k : Nat} (env : Fin k → M.Carrier .set) (pr ps f : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (restriction pr ps f) ↔
      Restriction (env pr) (env ps) (env f) := by
  simp only [restriction,Restriction,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    imageClass_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h c d => ⟨(h c d).1,(h c d).2⟩,fun h c d => ⟨(h c d).mp,(h c d).mpr⟩⟩

theorem exists_restriction (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W g r s X Y Q T pr ps : M.Carrier .set}
    (hXY : Subset X Y) (hpr : MapsTo X Q pr) (hps : MapsTo Y T ps)
    (hQ : Classes R env W g r X Q) (hPr : Projection R env W g r X pr)
    (hEr : EqualityLaw R env W g r pr) (hEs : EqualityLaw R env W g s ps)
    (hpreserve : ∀ sigma tau, EqG R env W g r sigma tau → EqG R env W g s sigma tau) :
    ∃ f, MapsTo Q T f ∧ Restriction pr ps f := by
  let params : Fin 2 → M.Carrier .set := args2 pr ps
  let query := imageClass (0 : Fin 4) 1 2 3
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := fun i => params i.rev, free := fun _ => Q }
  have hRel : ∀ c d, (ProjectSyntax.binary query).denote penv c d ↔ ImageClass pr ps c d := by
    intro c d
    rw [ForcingMapConditions.binary_semantics hM query params Q c d]
    simp only [ForcingMapConditions.MapRel,query,imageClass_semantics (M := M),params]
    rfl
  have ht : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c Q →
      ∃ d, (ProjectSyntax.binary query).denote penv c d := by
    intro c hc
    obtain ⟨sigma,hs,hsc⟩ := ForcingLocalQuotient.projection_onto hQ hPr hc
    obtain ⟨d,hsd,_⟩ := hps.1.2 sigma (hXY sigma hs)
    exact ⟨d,(hRel c d).mpr ⟨sigma,hsc,hsd⟩⟩
  have hu : ∀ c d e, (ProjectSyntax.binary query).denote penv c d →
      (ProjectSyntax.binary query).denote penv c e → d = e := by
    intro c d e hd he
    obtain ⟨sigma,hsc,hsd⟩ := (hRel c d).mp hd
    obtain ⟨tau,htc,hte⟩ := (hRel c e).mp he
    exact (hEs sigma tau d e hsd hte).mpr (hpreserve sigma tau ((hEr sigma tau c c hsc htc).mp rfl))
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv (source := Q) (target := T)
    ht (fun c _ d e hd he => hu c d e hd he) (by
      intro c d _ hd
      obtain ⟨sigma,_,hsd⟩ := (hRel c d).mp hd
      exact hps.2 sigma d hsd)
  refine ⟨f,(ForcingSupportSize.native_mapsTo hM Q T f).mpr hf,?_⟩
  intro c d
  exact (he c d).trans ⟨fun h => (hRel c d).mp h.2,fun h => by
    obtain ⟨sigma,hsc,hsd⟩ := h
    exact ⟨hpr.2 sigma c hsc,(hRel c d).mpr ⟨sigma,hsc,hsd⟩⟩⟩

theorem restrict_ofName {pr ps f sigma c d : M.Carrier .set}
    (hf : Restriction pr ps f) (hc : PureKuratowski.PairMember M sigma c pr)
    (hd : PureKuratowski.PairMember M sigma d ps) : PureKuratowski.PairMember M c d f :=
  (hf c d).mpr ⟨sigma,hc,hd⟩

theorem restrict_refl {k : Nat} {R : Formula (k+2)} {env : Fin k → M.Carrier .set}
    {W g r X Q pr f : M.Carrier .set}
    (hpr : MapsTo X Q pr) (hQ : Classes R env W g r X Q) (hPr : Projection R env W g r X pr)
    (hf : Restriction pr pr f) : ForcingConditionGraphs.IdentityGraph Q f := by
  intro c d
  constructor
  · intro hcd
    obtain ⟨sigma,hsc,hsd⟩ := (hf c d).mp hcd
    exact ⟨hpr.2 sigma c hsc,ForcingConditionGraphs.function_unique hpr.1 hsc hsd⟩
  · rintro ⟨hc,rfl⟩
    obtain ⟨sigma,_,hsc⟩ := ForcingLocalQuotient.projection_onto hQ hPr hc
    exact (hf c c).mpr ⟨sigma,hsc,hsc⟩

/-- Compose the actual descended function graphs; the same representative
witness gives the direct restriction. No quotient representative is chosen. -/
theorem restrict_restrict {X Y Z Q T U pr ps pt f g h : M.Carrier .set}
    (hXY : Subset X Y) (hYZ : Subset Y Z)
    (hpr : MapsTo X Q pr) (hps : MapsTo Y T ps) (hpt : MapsTo Z U pt)
    (hg : MapsTo T U g) (hf : Restriction pr ps f) (hG : Restriction ps pt g)
    (hh : Restriction pr pt h) : ForcingConditionGraphs.CompositionGraph Q g f h := by
  intro c e
  constructor
  · intro hce
    obtain ⟨sigma,hsc,hse⟩ := (hh c e).mp hce
    have hsX := ForcingConditionGraphs.function_input hpr.1 hsc
    obtain ⟨d,hsd,_⟩ := hps.1.2 sigma (hXY sigma hsX)
    exact ⟨hpr.2 sigma c hsc,d,(hf c d).mpr ⟨sigma,hsc,hsd⟩,(hG d e).mpr ⟨sigma,hsd,hse⟩⟩
  · rintro ⟨_,d,hcd,hde⟩
    obtain ⟨sigma,hsc,hsd⟩ := (hf c d).mp hcd
    have hsX := ForcingConditionGraphs.function_input hpr.1 hsc
    obtain ⟨e',hse',_⟩ := hpt.1.2 sigma (hYZ sigma (hXY sigma hsX))
    have hde' := (hG d e').mpr ⟨sigma,hsd,hse'⟩
    have he := ForcingConditionGraphs.function_unique hg.1 hde' hde
    exact (hh c e).mpr ⟨sigma,hsc,he ▸ hse'⟩

/-- Actual source roots: range monotonicity gives LocalName inclusion, and
local atomic monotonicity gives well-definedness on the constructed classes. -/
theorem actual_restriction (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r s G F nameBound J L HJ HL X Y Q T pr ps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hs : ForcingSupportSize.Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (hJ : ForcingSupportedNames.Range (env (rho 0)) r J)
    (hL : ForcingSupportedNames.Range (env (rho 0)) s L)
    (hHJ : ForcingLabelPermutations.Fixing G J HJ) (hHL : ForcingLabelPermutations.Fixing G L HL)
    (hX : ForcingLocalNames.Carrier (fun i => env (rho i)) G F nameBound HJ X)
    (hY : ForcingLocalNames.Carrier (fun i => env (rho i)) G F nameBound HL Y)
    (hpr : MapsTo X Q pr) (hps : MapsTo Y T ps)
    (hQ : Classes (orderFormula (rho 0) mul) env (env (rho 6)) g r X Q)
    (hPr : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X pr)
    (hPs : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g s Y ps) :
    ∃ f, MapsTo Q T f ∧ Restriction pr ps f := by
  have hJL : Subset J L := fun x hx => (hL x).mpr
    (ConstructionDescentPlacement.range_antitone hsr ((hJ x).mp hx))
  have hXY := ForcingLocalNames.restrict_name hHJ hHL hJL hX hY
  exact exists_restriction hM hXY hpr hps hQ hPr
    (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hr hPr)
    (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hs hPs)
    (fun _ _ he => ForcingLocalAtomic.eqG_restrict hM env rho mul hm hp hg hs hsr he)


def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp ((Source.SetLanguage.injection r (rho 0) I).imp ((Source.SetLanguage.injection s (rho 0) I).imp ((ForcingDiagramOrder.le (rho 0) mul s r).imp ((ForcingSupportedNames.range (rho 0) r J).imp ((ForcingSupportedNames.range (rho 0) s L).imp ((ForcingLabelPermutations.fixing G J HJ).imp ((ForcingLabelPermutations.fixing G L HL).imp ((ForcingLocalNames.carrier rho G F nameBound HJ X).imp ((ForcingLocalNames.carrier rho G F nameBound HL Y).imp ((Source.SetLanguage.mapsTo pr X Q).imp ((Source.SetLanguage.mapsTo ps Y T).imp ((ForcingLocalQuotient.classes (orderFormula (rho 0) mul) id (rho 6) g r X Q).imp ((ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g r X pr).imp ((ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g s Y ps).imp ((.ex ((Source.SetLanguage.mapsTo (Fin.last k) Q.castSucc T.castSucc).conj
    (restriction pr.castSucc ps.castSucc (Fin.last k)))))))))))))))))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg hr hs hsr hJ hL hHJ hHL hX hY hpr hps hQ hPr hPs
  obtain ⟨f,hf,he⟩ := actual_restriction hM env rho mul
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)
    ((ForcingSupportSize.injection_semantics (M := M) env s (rho 0) I).mp hs)
    ((ForcingDiagramOrder.le_semantics (M := M) env (rho 0) mul s r).mp hsr)
    ((ForcingSupportedNames.range_semantics (M := M) env (rho 0) r J).mp hJ)
    ((ForcingSupportedNames.range_semantics (M := M) env (rho 0) s L).mp hL)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G J HJ).mp hHJ)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G L HL).mp hHL)
    ((ForcingLocalNames.carrier_semantics (M := M) env rho G F nameBound HJ X).mp hX)
    ((ForcingLocalNames.carrier_semantics (M := M) env rho G F nameBound HL Y).mp hY)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env ps Y T).mp hps)
    ((ForcingLocalQuotient.classes_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g r X Q).mp hQ)
    ((ForcingLocalQuotient.projection_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g r X pr).mp hPr)
    ((ForcingLocalQuotient.projection_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6) g s Y ps).mp hPs)
  refine ⟨f,?_,?_⟩
  · apply (ForcingSupportSize.mapsTo_semantics (M := M) (Fin.lastCases f env)
      (Fin.last k) Q.castSucc T.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hf
  · apply (restriction_semantics (M := M) (Fin.lastCases f env)
      pr.castSucc ps.castSucc (Fin.last k)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using he

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (constructionSentence rho I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps hM)

def identitySentence {k : Nat} (R : Formula (k+2)) (W g r X Q pr f : Fin k) : Source.Sentence :=
  ((Source.SetLanguage.mapsTo pr X Q).imp
    ((ForcingLocalQuotient.classes R id W g r X Q).imp
      ((ForcingLocalQuotient.projection R id W g r X pr).imp
        ((restriction pr pr f).imp (ForcingConditionGraphs.identityGraph Q f))))).close

theorem identity_models {k : Nat} (R : Formula (k+2)) (W g r X Q pr f : Fin k)
    (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (identitySentence R W g r X Q pr f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpr hQ hPr hf
  exact (ForcingConditionGraphs.identityGraph_semantics (M := M) env Q f).mpr
    (restrict_refl
      ((ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr)
      ((ForcingLocalQuotient.classes_semantics (M := M) env R id W g r X Q).mp hQ)
      ((ForcingLocalQuotient.projection_semantics (M := M) env R id W g r X pr).mp hPr)
      ((restriction_semantics (M := M) env pr pr f).mp hf))

theorem identity_kernel_certificate {k : Nat} (R : Formula (k+2)) (W g r X Q pr f : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (identitySentence R W g r X Q pr f)) :=
  ModelTransfer.derives (fun _ hM => identity_models R W g r X Q pr f hM)

def compositionSentence {k : Nat} (X Y Z Q T U pr ps pt f g h : Fin k) : Source.Sentence :=
  ((Source.SetLanguage.subset X Y).imp ((Source.SetLanguage.subset Y Z).imp ((Source.SetLanguage.mapsTo pr X Q).imp ((Source.SetLanguage.mapsTo ps Y T).imp ((Source.SetLanguage.mapsTo pt Z U).imp ((Source.SetLanguage.mapsTo g T U).imp ((restriction pr ps f).imp ((restriction ps pt g).imp ((restriction pr pt h).imp (ForcingConditionGraphs.compositionGraph Q g f h)))))))))).close

theorem composition_models {k : Nat} (X Y Z Q T U pr ps pt f g h : Fin k)
    (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (compositionSentence X Y Z Q T U pr ps pt f g h)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hXY hYZ hpr hps hpt hg hf hG hh
  apply (ForcingConditionGraphs.compositionGraph_semantics (M := M) env Q g f h).mpr
  exact restrict_restrict
    ((ForcingLabelPermutations.subset_semantics (M := M) env X Y).mp hXY)
    ((ForcingLabelPermutations.subset_semantics (M := M) env Y Z).mp hYZ)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env pr X Q).mp hpr)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env ps Y T).mp hps)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env pt Z U).mp hpt)
    ((ForcingSupportSize.mapsTo_semantics (M := M) env g T U).mp hg)
    ((restriction_semantics (M := M) env pr ps f).mp hf)
    ((restriction_semantics (M := M) env ps pt g).mp hG)
    ((restriction_semantics (M := M) env pr pt h).mp hh)

theorem composition_kernel_certificate {k : Nat} (X Y Z Q T U pr ps pt f g h : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (compositionSentence X Y Z Q T U pr ps pt f g h)) :=
  ModelTransfer.derives (fun _ hM => composition_models X Y Z Q T U pr ps pt f g h hM)

def representativeSentence : Source.Sentence :=
  ((restriction (0 : Fin 6) 1 2).imp ((Source.SetLanguage.edge 0 3 4).imp
    ((Source.SetLanguage.edge 1 3 5).imp (Source.SetLanguage.edge 2 4 5)))).close

theorem representative_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence representativeSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf hc hd
  exact (KuratowskiZF.source_edge (M := M) env 2 4 5).mpr (restrict_ofName
    ((restriction_semantics (M := M) env 0 1 2).mp hf)
    ((KuratowskiZF.source_edge (M := M) env 0 3 4).mp hc)
    ((KuratowskiZF.source_edge (M := M) env 1 3 5).mp hd))

theorem representative_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence representativeSentence) :=
  ModelTransfer.derives (fun _ hM => representative_models hM)

end PPAC.Migration.ForcingLocalRestriction
