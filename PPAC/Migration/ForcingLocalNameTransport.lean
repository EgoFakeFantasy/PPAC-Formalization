/- Pinned QuotientTransport.LocalName.transportEquiv:52-61, consuming
LocalQuotients.LocalName/transport. Reuse existing bound stability, HS action,
fixing-subgroup conjugacy and name inverse. No alternate name carrier. -/
import PPAC.Migration.ForcingLocalTransport

namespace PPAC.Migration.ForcingLocalNameTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingConditionGraphs (Permutation)
open ForcingSupportSize (Injection)
open ForcingStabilizerTransport (Image)
open ForcingProductCovariance (SystemData)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingStabilizer (Action)
open ForcingSupportedNames (Supported)
open ForcingLocalNames (LocalName Carrier)
open ForcingPowerName (Bound Subset)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem bound_supported (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F labels bound : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G)
    (hHS : ForcingHS.HS actionFormula v G (v 6) F labels) (hFix : Supported v G labels)
    (hBound : Bound (v 6) labels bound) : Supported v G bound := by
  obtain ⟨S,b,hS,_,_,hb,hStable⟩ := ForcingPowerName.exists_bound hM v hp hG hHS
  have he : b = bound := (ModelTransfer.extensionality hM).eq_of_same_members b bound
    (fun z => (hb z).trans (hBound z).symm)
  subst b
  intro pi hpi a ha
  exact hStable pi ((hS pi).mpr ⟨hpi,a,ha,hFix pi hpi a ha⟩) a ha

theorem reverse_data (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai : M.Carrier .set}
    (h : SystemData v I K B w G F mu pi inv c a ai) :
    ∃ d, SystemData v I K B w G F mu inv pi d ai a := by
  obtain ⟨hp,hG,hpi,hinv,hpii,_,_,ha,hai,hF⟩ := h
  have hi : ForcingConditionGraphs.InverseGraph inv pi := fun x y => (hpii y x).symm
  obtain ⟨d,hd,hdg⟩ := ForcingConjugationGraph.exists_graph hM hG hinv hpi hi
  exact ⟨d,hp,hG,hinv,hpi,hi,hd,hdg,hai,ha,hF⟩

theorem local_name_move (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai bound J JT H HT nu out : M.Carrier .set}
    (hData : SystemData v I K B w G F mu pi inv c a ai)
    (hBound : Supported v G bound) (hJ : Subset J I) (hImage : Image pi J JT)
    (hH : ForcingLabelPermutations.Fixing G J H) (hHT : ForcingLabelPermutations.Fixing G JT HT)
    (hn : LocalName v G F bound H nu) (hAct : Action (v 6) a nu out) : LocalName v G F bound HT out := by
  have hc := ForcingProductCovariance.context_of_data hM hData
  obtain ⟨hp,hG,hpi,hinv,hpii,hcPerm,hcg,ha,_,_⟩ := hData
  have hFixImage := ForcingConjugationGraph.fixing_image hG hpi hinv.1 hpii hcPerm hcg hImage hJ hH hHT
  have hb := hBound pi ((hG pi).mpr hpi) a ((mapRel_action v pi a).mpr ha)
  refine ⟨⟨ForcingHSAction.hs_action hM hc nu hn.1.1 out hAct,
    ForcingPowerName.map_subset hM hc.2.2.1.1 hn.1.2 hAct hb⟩,?_⟩
  intro t ht actT hat
  obtain ⟨s,hs,hst⟩ := (hFixImage t).mp ht
  have hsG := ((hH s).mp hs).1
  have htG := ((hHT t).mp ht).1
  obtain ⟨actS,has⟩ := hc.1.1 s hsG
  have hFixed : ForcingStabilizer.Fixed actionFormula v (v 6) nu s := ⟨actS,has,hn.2 s hs actS has⟩
  obtain ⟨bt,hbt,hfix⟩ := (ForcingStabilizerTransport.fixed_transport hM hc.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.1 hsG htG hst (ForcingHS.isName hn.1.1) hAct).mp hFixed
  have he := ForcingProductFamily.unique hM ((mapRel_action v t bt).mp hbt) ((mapRel_action v t actT).mp hat)
  subst bt
  exact hfix

/-- The graph of the literal raw name action, restricted to the actual source carrier. -/
def Graph (W a X f : M.Carrier .set) : Prop := ∀ nu out,
  PureKuratowski.PairMember M nu out f ↔ (Project.FirstOrderSemantics.reduct M).mem nu X ∧ Action W a nu out

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai bound J JT H HT X Y : M.Carrier .set}
    (hData : SystemData v I K B w G F mu pi inv c a ai)
    (hBound : Supported v G bound) (hJ : Subset J I) (hImage : Image pi J JT)
    (hH : ForcingLabelPermutations.Fixing G J H) (hHT : ForcingLabelPermutations.Fixing G JT HT)
    (hX : Carrier v G F bound H X) (hY : Carrier v G F bound HT Y) :
    ∃ f, Injection X Y f ∧ Graph (v 6) a X f ∧
      ∀ out, (Project.FirstOrderSemantics.reduct M).mem out Y →
        ∃ nu, (Project.FirstOrderSemantics.reduct M).mem nu X ∧ PureKuratowski.PairMember M nu out f := by
  have hc := ForcingProductCovariance.context_of_data hM hData
  let params := args2 (v 6) a
  let query : Formula 4 := ForcingStabilizer.action 0 1 2 3
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := fun j => params j.rev, free := fun _ => X }
  have he nu out : (ProjectSyntax.binary query).denote env nu out ↔ Action (v 6) a nu out := by
    rw [ForcingMapConditions.binary_semantics hM query params X nu out]
    simp only [ForcingMapConditions.MapRel,query,ForcingStabilizer.action_semantics (M := M)]
    rfl
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env (source := X) (target := Y)
    (fun nu _ => by
      obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM hc.2.2.1.1 nu
      exact ⟨out,(he nu out).mpr hout⟩)
    (fun nu _ x y hx hy => ForcingNameConjugacy.unique hM hc.2.2.1.1 ((he nu x).mp hx) ((he nu y).mp hy))
    (fun nu out hnu hout => (hY out).mpr (local_name_move hM hData hBound hJ hImage hH hHT ((hX nu).mp hnu) ((he nu out).mp hout)))
  have hGraph : Graph (v 6) a X f := fun nu out => (hEdge nu out).trans (and_congr Iff.rfl (he nu out))
  refine ⟨f,⟨(ForcingSupportSize.native_mapsTo hM X Y f).mpr hf,?_⟩,hGraph,?_⟩
  · intro x y z hx hy
    obtain ⟨hx,hxz⟩ := (hGraph x z).mp hx
    obtain ⟨hy,hyz⟩ := (hGraph y z).mp hy
    exact ForcingNameConjugacy.injective hM hc.2.2.1 (ForcingHS.isName ((hX x).mp hx).1.1)
      (ForcingHS.isName ((hX y).mp hy).1.1) hxz hyz
  · intro out hout
    obtain ⟨d,hReverse⟩ := reverse_data hM hData
    have hRC := ForcingProductCovariance.context_of_data hM hReverse
    obtain ⟨nu,hnu⟩ := ForcingNameConjugacy.exists_action hM hRC.2.2.1.1 out
    have hpi := hData.2.2.1
    have hJT : Subset JT I := by
      intro t ht
      obtain ⟨s,_,hst⟩ := (hImage t).mp ht
      exact hpi.1.2 s t hst
    have hInvImage := ForcingCohenOrderAction.reverse_image hpi hData.2.2.2.2.1 hJ hImage
    have hnuLocal := local_name_move hM hReverse hBound hJT hInvImage hHT hH ((hY out).mp hout) hnu
    have hBack := ForcingNameConjugacy.inverse_action hM hRC.2.2.1.1 hc.2.2.1.1
      (fun x y => (hc.2.2.2.2.1 y x).symm) (ForcingHS.isName ((hY out).mp hout).1.1) hnu
    exact ⟨nu,(hX nu).mpr hnuLocal,(hGraph nu out).mpr ⟨(hX nu).mpr hnuLocal,hBack⟩⟩


def Transport (v : Fin 7 → M.Carrier .set) (G F bound pi a J : M.Carrier .set) : Prop :=
  ∃ JT H HT X Y f, Image pi J JT ∧ ForcingLabelPermutations.Fixing G J H ∧
    ForcingLabelPermutations.Fixing G JT HT ∧ Carrier v G F bound H X ∧ Carrier v G F bound HT Y ∧
    Injection X Y f ∧ Graph (v 6) a X f ∧
    ∀ out, (Project.FirstOrderSemantics.reduct M).mem out Y →
      ∃ nu, (Project.FirstOrderSemantics.reduct M).mem nu X ∧ PureKuratowski.PairMember M nu out f

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai bound J : M.Carrier .set}
    (hData : SystemData v I K B w G F mu pi inv c a ai) (hBound : Supported v G bound) (hJ : Subset J I) :
    Transport v G F bound pi a J := by
  obtain ⟨JT,hJT,_⟩ := ForcingLabelConjugacy.exists_image hM hData.2.2.1.1 (J := J)
  obtain ⟨H,hH⟩ := ForcingLabelPermutations.exists_fixing hM G J
  obtain ⟨HT,hHT⟩ := ForcingLabelPermutations.exists_fixing hM G JT
  obtain ⟨X,hX⟩ := ForcingLocalNames.exists_carrier hM v G F bound H
  obtain ⟨Y,hY⟩ := ForcingLocalNames.exists_carrier hM v G F bound HT
  obtain ⟨f,hf,hGraph,hOnto⟩ := exists_graph hM hData hBound hJ hJT hH hHT hX hY
  exact ⟨JT,H,HT,X,Y,f,hJT,hH,hHT,hX,hY,hf,hGraph,hOnto⟩

/-- Actual labelSet and its exact subsetBound discharge the stability input. -/
theorem literal_construct (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai labelMap top bit labels bound J : M.Carrier .set}
    (hData : SystemData v I K B w G F mu pi inv c a ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hNormal : ForcingNormalFilter.Normal I G F) (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap)
    (hTop : ForcingWithTopCarrier.Empty top) (hLabels : ForcingLabelSet.LabelSet (v 6) I K labelMap top bit labels)
    (hBound : Bound (v 6) labels bound) (hJ : Subset J I) : Transport v G F bound pi a J := by
  have hG := hData.2.1
  have hF := hData.2.2.2.2.2.2.2.2.2
  obtain ⟨hHS,hFix⟩ := ForcingLabelSet.HS_and_fixed hM v hData.1 hG hNormal hF hw hSmall hLabelMap hTop hLabels
  exact construct hM hData (bound_supported hM hData.1 hG hHS hFix hBound) hJ


theorem range_image {D pi r R J JT : M.Carrier .set} (hJ : ForcingSupportedNames.Range D r J)
    (hComp : ForcingConditionGraphs.CompositionGraph D pi r R) (hImage : Image pi J JT) :
    ForcingSupportedNames.Range D R JT := by
  intro y
  constructor
  · intro hy
    obtain ⟨x,hx,hxy⟩ := (hImage y).mp hy
    obtain ⟨k,hk,hkx⟩ := (hJ x).mp hx
    exact ⟨k,hk,(hComp k y).mpr ⟨hk,x,hkx,hxy⟩⟩
  · rintro ⟨k,hk,hky⟩
    obtain ⟨_,x,hkx,hxy⟩ := (hComp k y).mp hky
    exact (hImage y).mpr ⟨x,(hJ x).mpr ⟨k,hk,hkx⟩,hxy⟩

def graph {m : Nat} (W a X f : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc X.castSucc.castSucc).conj
      (ForcingStabilizer.action W.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (W a X f : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (graph W a X f) ↔ Graph (env W) (env a) (env X) (env f) := by
  simp only [graph,Graph,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,ForcingStabilizer.action_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x y => ⟨(h x y).1,(h x y).2⟩,fun h x y => ⟨(h x y).mp,(h x y).mpr⟩⟩

def transport {m : Nat} (rho : Fin 7 → Fin m) (G F bound pi a J : Fin m) : Formula m :=
  let up := fun i : Fin m => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr := fun j => up (rho j)
  let JT := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
  let H := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc
  let HT := (Fin.last (m+2)).castSucc.castSucc.castSucc
  let X := (Fin.last (m+3)).castSucc.castSucc
  let Y := (Fin.last (m+4)).castSucc
  let f := Fin.last (m+5)
  let onto : Formula (m+6) :=
    .all ((Formula.mem (Fin.last (m+6)) Y.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+7)) X.castSucc.castSucc).conj
        (Source.SetLanguage.edge f.castSucc.castSucc (Fin.last (m+7)) ((Fin.last (m+6)).castSucc)))))
  let body := (ForcingStabilizerTransport.image (up pi) (up J) JT).conj
    ((ForcingLabelPermutations.fixing (up G) (up J) H).conj
      ((ForcingLabelPermutations.fixing (up G) JT HT).conj
        ((ForcingLocalNames.carrier rr (up G) (up F) (up bound) H X).conj
          ((ForcingLocalNames.carrier rr (up G) (up F) (up bound) HT Y).conj
            ((Source.SetLanguage.injection f X Y).conj
              ((graph (up (rho 6)) (up a) X f).conj onto))))))
  .ex (.ex (.ex (.ex (.ex (.ex body)))))

theorem transport_semantics {m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin m) (G F bound pi a J : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (transport rho G F bound pi a J) ↔
      Transport (fun j => env (rho j)) (env G) (env F) (env bound) (env pi) (env a) (env J) := by
  simp only [transport,Transport,Formula.Realize,ForcingStabilizerTransport.image_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingLocalNames.carrier_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),graph_semantics (M := M),KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c a ai bound J : Fin k) : Source.Sentence :=
  ((ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai).imp
    ((ForcingEquivariantMix.fixedAll rho G bound).imp ((Source.SetLanguage.subset J I).imp (transport rho G F bound pi a J)))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c a ai bound J : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w G F mu pi inv c a ai bound J)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hData hBound hJ
  exact (transport_semantics env rho G F bound pi a J).mpr (construct hM
    ((ForcingProductCovariance.systemData_semantics (M := M) env rho I K B w G F mu pi inv c a ai).mp hData)
    ((ForcingSupportedNames.supported_semantics (M := M) env rho G bound).mp hBound)
    ((ForcingLabelPermutations.subset_semantics (M := M) env J I).mp hJ))

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c a ai bound J : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w G F mu pi inv c a ai bound J)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w G F mu pi inv c a ai bound J hM)

def literalSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mu pi inv c a ai labelMap top bit labels bound J : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai))
      (.imp (Project.Formula.isOmega (.bound w))
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
          (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
            (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
              (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
                (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
                  (.imp (ProjectSyntax.encode id (ForcingLabelBound.bound (rho 6) labels bound))
                    (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset J I))
                      (ProjectSyntax.encode id (transport rho G F bound pi a J)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed]

theorem literal_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mu pi inv c a ai labelMap top bit labels bound J : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (literalSentence rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (literalSentence rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.bound_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),transport_semantics (M := M)]
  exact literal_construct hM

theorem literal_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mu pi inv c a ai labelMap top bit labels bound J : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (literalSentence rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J)) :=
  ModelTransfer.derives (fun _ hM => literal_models rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J hM)

end PPAC.Migration.ForcingLocalNameTransport
