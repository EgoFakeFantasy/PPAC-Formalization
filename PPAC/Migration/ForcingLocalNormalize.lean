/- Pinned LocalQuotients.separate_fixed:218, normalize_fixed:226,
localNormalize:327 and localNormalize_eq:333. Preserve the source separated
name and reuse test_permute/CollectedHS.fixed and PowerName normalization. -/
import PPAC.Migration.ForcingLocalNames

namespace PPAC.Migration.ForcingLocalNormalize
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingSupportedNames (Supported)
open ForcingSeparation (Separated testFormula)
open ForcingHS (HS)
open ForcingAtomicRelations (Forces)
open ForcingPowerName (Bound Subset SubsetF)
open ForcingLocalNames (LocalName)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source common-support argument, specialized to an arbitrary internal
subgroup. The actual separated name is constructed; its support is proved. -/
theorem separate_supported (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma : Fin k)
    {I K B w H : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup I (env G) H)
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma))
    (hfixed : Supported (fun j => env (rho j)) H (env sigma))
    (v : Fin n → Fin k)
    (hv : ∀ j, HS actionFormula (fun l => env (rho l)) (env G) (env (rho 6)) (env F) (env (v j)))
    (hvfixed : ∀ j, Supported (fun l => env (rho l)) H (env (v j)))
    (phi : Formula (n+1)) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Separated (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (v j))
        (env (rho 6)) (env sigma) name phi ∧ Supported (fun j => env (rho j)) H name := by
  let R := orderFormula (rho 0) mul
  let J := domain rho G F
  let T := testFormula R J v (rho 6) sigma phi
  obtain ⟨f,name,hf,hn,hHS⟩ := ForcingSeparation.exists_separate hM env rho G F mul sigma hp hG hF hs v hv phi
  have hfamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma) f := by
    intro i child _ hic
    obtain ⟨hi,c,hcode⟩ := (hf i child).mp hic
    exact ForcingHS.child hs ⟨i,hcode,hi⟩
  have hperm : ForcingCollectedHS.Permutes T env (fun j => env (rho j)) H (env sigma) f (env (rho 6)) := by
    intro g hg a hga child p image q had him hpq
    obtain ⟨hcond,i,_,hic,ht⟩ := had
    obtain ⟨j,hj,hji,hT⟩ := ForcingSeparation.test_permute hM env rho G F mul hp hG hF
      ((hG g).mp (hH.1 g hg)) hga hs hf (hfixed g hg a hga) (fun j => env (v j))
      (fun j => hvfixed j g hg a hga) phi hic
      ((ForcingSeparation.testFormula_semantics env R J v (rho 6) sigma phi i p).mp ht) him hcond hpq
    exact ⟨(ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)).1.2 p q hpq,
      j,hj,hji,(ForcingSeparation.testFormula_semantics env R J v (rho 6) sigma phi j q).mpr hT⟩
  exact ⟨name,hHS,ForcingSeparation.edge_separate hM hf hn,
    fun g hg a hga => ForcingCollectedHS.fixed hM T env (fun j => env (rho j))
      hp hG hH hfamily hperm hn hg hga⟩

/-- Source normalize_fixed and localNormalize, retaining the exact separated
constructor so the existing boundedness and equality lemmas apply to it. -/
theorem exists_normalize (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma nu : Fin k)
    {I K B w H bound : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup I (env G) H)
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma))
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env nu))
    (hsfixed : Supported (fun j => env (rho j)) H (env sigma))
    (hnfixed : Supported (fun j => env (rho j)) H (env nu))
    (hb : Bound (env (rho 6)) (env sigma) bound) :
    ∃ name, LocalName (fun j => env (rho j)) (env G) (env F) bound H name ∧
      Separated (orderFormula (rho 0) mul) (domain rho G F) env (fun _ : Fin 1 => env nu)
        (env (rho 6)) (env sigma) name (.mem (1 : Fin 2) 0) := by
  obtain ⟨name,hn,hsep,hfixed⟩ := separate_supported hM env rho G F mul sigma hp hG hF hH hs hsfixed
    (fun _ : Fin 1 => nu) (fun _ => hnu) (fun _ => hnfixed) (.mem (1 : Fin 2) 0)
  exact ⟨name,⟨⟨hn,ForcingPowerName.normalized_bounded hb hn hsep⟩,hfixed⟩,hsep⟩

theorem normalize_eq (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {sigma nu name bound H p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu)
    (hn : LocalName (fun j => env (rho j)) (env G) (env F) bound H name)
    (hsep : Separated (orderFormula (rho 0) mul) (domain rho G F) env (fun _ : Fin 1 => nu)
      (env (rho 6)) sigma name (.mem (1 : Fin 2) 0))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hsub : SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p nu sigma) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) nu name p := by
  apply ForcingPowerName.normalize_eq hM env rho G F mul hpre hnu hn.1.1 hp _ hsub
  intro child q hq
  simpa only [ForcingFormula.force_mem,show (1 : Fin 2) = Fin.last 1 from rfl,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc] using
    ForcingSeparationAxiom.mem_separate hM hpre hsep hq (nu := child)

/-- Concrete source localNormalize: actual labelSet, exact bound and fixing
graph. The labelSet's HS/full-group fixation and subgroup facts are derived. -/
theorem actual_normalize (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma nu : Fin k)
    {I K B w mu c t b J H bound e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hs : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b (env sigma))
    (hb : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b bound)
    (hJI : Subset J I) (hFix : ForcingLabelPermutations.Fixing (env G) J H)
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env nu))
    (hnfixed : Supported (fun j => env (rho j)) H (env nu)) :
    ∃ name, LocalName (fun j => env (rho j)) (env G) (env F) bound H name ∧
      Separated (orderFormula (rho 0) mul) (domain rho G F) env (fun _ : Fin 1 => env nu)
        (env (rho 6)) (env sigma) name (.mem (1 : Fin 2) 0) ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p (env nu) (env sigma) →
        Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env nu) name p := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hH := ForcingConjugationGraph.fixing_subgroup hM hG hFix hJI
  obtain ⟨hHS,hFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw
    ((ForcingSupportSize.native_small hM w mu).mpr hMu.2) hc ht hs
  obtain ⟨name,hn,hsep⟩ := exists_normalize hM env rho G F mul sigma nu hp hG hNormal hH hHS hnu
    (fun g hg a hga => hFixed g (hH.1 g hg) a hga) hnfixed ((ForcingLabelBound.bound_iff hM hs).mpr hb)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨name,hn,hsep,fun _ hp hsub => normalize_eq hM env rho G F mul hpre hnu hn hsep hp hsub⟩


/-- One constructed normalization, with exact separated edges and equality at
every condition which forces the input to be a subset of the actual labelSet. -/
def result {k : Nat} (rho : Fin 7 → Fin k) (G F mul sigma nu bound H : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let D := domain rho G F
  .ex ((ForcingLocalNames.localName (paramsUp rho) G.castSucc F.castSucc bound.castSucc H.castSucc (Fin.last k)).conj
    ((ForcingSeparation.separated R D Fin.castSucc (fun _ : Fin 1 => nu.castSucc)
      (rho 6).castSucc sigma.castSucc (Fin.last k) (.mem (1 : Fin 2) 0)).conj
      (.all ((Formula.mem (Fin.last (k+1)) (rho 6).castSucc.castSucc).imp
        ((ForcingPowerName.subsetF R D (fun j => j.castSucc.castSucc) (rho 6).castSucc.castSucc
          (Fin.last (k+1)) nu.castSucc.castSucc sigma.castSucc.castSucc).imp
          (ForcingAtomicRelations.forces true R (fun j => j.castSucc.castSucc) (rho 6).castSucc.castSucc
            nu.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))))))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul sigma nu bound H : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (result rho G F mul sigma nu bound H) ↔
    ∃ name, LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env H) name ∧
      Separated (orderFormula (rho 0) mul) (domain rho G F) env (fun _ : Fin 1 => env nu)
        (env (rho 6)) (env sigma) name (.mem (1 : Fin 2) 0) ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p (env nu) (env sigma) →
        Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env nu) name p := by
  simp only [result,Formula.Realize,ForcingLocalNames.localName_semantics (M := M),
    ForcingSeparation.separated_semantics (M := M),ForcingPowerName.subsetF_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu c t b J H bound e G F mul sigma nu : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
        (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
          (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
            (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
              (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
                (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
                  (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
                    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b sigma))
                      (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b bound))
                        (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset J I))
                          (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G J H))
                            (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F nu))
                              (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho H nu))
                                (ProjectSyntax.encode id (result rho G F mul sigma nu bound H))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu c t b J H bound e G F mul sigma nu : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w mu c t b J H bound e G F mul sigma nu)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho I K B w mu c t b J H bound e G F mul sigma nu)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    result_semantics (M := M),Project.Term.eval_bound]
  intro hw hMu hm hp hG hF hc ht hs hb hJI hFix hnu hnfixed
  exact actual_normalize hM env rho G F mul sigma nu hw hMu hm hp hG hF hc ht hs hb hJI hFix hnu hnfixed

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu c t b J H bound e G F mul sigma nu : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence rho I K B w mu c t b J H bound e G F mul sigma nu)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mu c t b J H bound e G F mul sigma nu hM)


/-- Value-slot adaptation of the proved concrete normalization. Reuse the
existing relation/domain congruence; this introduces no new normalization. -/
theorem normalize_at_values (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu c t b J H bound e sigma nu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hs : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b sigma)
    (hb : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b bound)
    (hJI : Subset J I) (hFix : ForcingLabelPermutations.Fixing (env G) J H)
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu)
    (hnfixed : Supported (fun j => env (rho j)) H nu) :
    ∃ name, LocalName (fun j => env (rho j)) (env G) (env F) bound H name ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p nu sigma →
        Forces true (orderFormula (rho 0) mul) env (env (rho 6)) nu name p := by
  let ext : Fin (k+2) → M.Carrier .set := Fin.lastCases nu (Fin.lastCases sigma env)
  let up : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let ra := fun j => up (rho j)
  have hCall := actual_normalize hM ext ra (up G) (up F) (up mul)
    (Fin.last k).castSucc (Fin.last (k+1)) (I := I) (K := K) (B := B) (w := w) (mu := mu)
    (c := c) (t := t) (b := b) (J := J) (H := H) (bound := bound) (e := e)
  simp only [ext,ra,up,Fin.lastCases_last,Fin.lastCases_castSucc] at hCall
  obtain ⟨name,hn,_,heq⟩ := hCall hw hMu hm hp hG hF hc ht hs hb hJI hFix hnu hnfixed
  have hR : ∀ x y, ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y ↔
      ForcingMapConditions.MapRel (orderFormula (ra 0) (up mul)) ext x y := by
    intro x y
    simp only [ForcingProductSymmetry.orderFormula_semantics,ext,ra,up,Fin.lastCases_castSucc]
  have hD : ∀ x, ForcingClassEvaluation.Predicate (domain rho G F) env x ↔
      ForcingClassEvaluation.Predicate (domain ra (up G) (up F)) ext x := by
    intro x
    simp only [ForcingPairUnion.domain_semantics,ext,ra,up,Fin.lastCases_castSucc]
  refine ⟨name,hn,?_⟩
  intro p hpW hsub
  exact (ForcingSeparation.atomic_congr hR true (env (rho 6)) nu name p).mpr
    (heq p hpW ((ForcingPowerName.subset_relation_congr hR hD (env (rho 6)) p nu sigma).mp hsub))

end PPAC.Migration.ForcingLocalNormalize
