/- Pinned ProductNames.labelSet/labelSet_raw/smul_labelSet (324-344).
Consumer: LocalQuotients.labelSet_subsetBound and localName_descent.
Construct the actual set-indexed graph of labels, collect at the real top,
and reuse collected HS/fixation. No supplied label family or rank cutoff. -/
import PPAC.Migration.ForcingLabelNames

namespace PPAC.Migration.ForcingLabelSet
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingConditionGraphs (FunctionOn)
open ForcingLabelNames (Label label)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Family (W I K c t b f : M.Carrier .set) : Prop :=
  FunctionOn I f ∧ ∀ j name, PureKuratowski.PairMember M j name f ↔
    (Project.FirstOrderSemantics.reduct M).mem j I ∧ Label W K c t j b name

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {K c : M.Carrier .set} (hc : FunctionOn K c) (W I t b : M.Carrier .set) :
    ∃ f, Family (M := M) W I K c t b f := by
  let params : Fin 5 → M.Carrier .set := Fin.cases W (Fin.cases K (args3 c t b))
  let query := label (0 : Fin 7) 1 2 3 5 4 6
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := fun i => params i.rev, free := fun _ => I }
  have hRel : ∀ j name, (ProjectSyntax.binary query).denote env j name ↔ Label W K c t j b name := by
    intro j name
    rw [ForcingMapConditions.binary_semantics hM query params I j name]
    simp only [MapRel,query,ForcingLabelNames.label_semantics (M := M),params]
    rfl
  have ht : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j I →
      ∃ name, (ProjectSyntax.binary query).denote env j name := by
    intro j _
    obtain ⟨name,hn⟩ := ForcingLabelNames.exists_label hM hc W t j b
    exact ⟨name,(hRel j name).mpr hn⟩
  have hu : ∀ j a n, (ProjectSyntax.binary query).denote env j a →
      (ProjectSyntax.binary query).denote env j n → a = n := by
    intro j a n ha hn
    exact ForcingLabelNames.unique hM ((hRel j a).mp ha) ((hRel j n).mp hn)
  obtain ⟨bound,hbound⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) env I ht hu
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (ProjectSyntax.binary query) env (source := I) (target := bound) ht
    (fun j _ a n ha hn => hu j a n ha hn)
    (fun j name hj hn => (hbound name).mpr ⟨j,hj,hn⟩)
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM I bound f).mpr hf).1,
    fun j name => (he j name).trans (and_congr Iff.rfl (hRel j name))⟩

def topPredicate : Formula 3 := .equal 2 0

theorem topPredicate_semantics (t j p : M.Carrier .set) :
    MapRel topPredicate (fun _ : Fin 1 => t) j p ↔ p = t := by
  rfl

def Entry (W I K c t b z : M.Carrier .set) : Prop :=
  ∃ child j, (Project.FirstOrderSemantics.reduct M).mem j I ∧ Label W K c t j b child ∧
    PureKuratowski.Code M z child t

def entry {k : Nat} (W I K c t b z : Fin k) : Formula k :=
  .ex (.ex ((Formula.mem (Fin.last (k+1)) I.castSucc.castSucc).conj
    ((label W.castSucc.castSucc K.castSucc.castSucc c.castSucc.castSucc t.castSucc.castSucc
      (Fin.last (k+1)) b.castSucc.castSucc (Fin.last k).castSucc).conj
        (PairSyntax.ordered z.castSucc.castSucc (Fin.last k).castSucc t.castSucc.castSucc))))

theorem entry_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W I K c t b z : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (entry W I K c t b z) ↔
      Entry (env W) (env I) (env K) (env c) (env t) (env b) (env z) := by
  simp only [entry,Entry,Formula.Realize,ForcingLabelNames.label_semantics (M := M),KuratowskiZF.source_code,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def LabelSet (W I K c t b name : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z name ↔ Entry W I K c t b z

def labelSet {k : Nat} (W I K c t b name : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) name.castSucc).iff
    (entry W.castSucc I.castSucc K.castSucc c.castSucc t.castSucc b.castSucc (Fin.last k)))

theorem labelSet_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W I K c t b name : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (labelSet W I K c t b name) ↔
      LabelSet (env W) (env I) (env K) (env c) (env t) (env b) (env name) := by
  simp only [labelSet,LabelSet,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1,(h z).2⟩,fun h z => ⟨(h z).mp,(h z).mpr⟩⟩

theorem collected_iff {W I K c t b f name : M.Carrier .set}
    (hf : Family W I K c t b f) (ht : (Project.FirstOrderSemantics.reduct M).mem t W) :
    ForcingCollectedName.Collected topPredicate (fun _ : Fin 1 => t) I f W name ↔ LabelSet W I K c t b name := by
  constructor
  · intro hn z
    constructor
    · intro hz
      obtain ⟨child,p,⟨_,j,hj,hjf,hr⟩,hcode⟩ := (hn z).mp hz
      have e := (topPredicate_semantics t j p).mp hr
      subst p
      exact ⟨child,j,hj,((hf.2 j child).mp hjf).2,hcode⟩
    · rintro ⟨child,j,hj,hl,hcode⟩
      exact (hn z).mpr ⟨child,t,⟨ht,j,hj,(hf.2 j child).mpr ⟨hj,hl⟩,
        (topPredicate_semantics t j t).mpr rfl⟩,hcode⟩
  · intro hn z
    constructor
    · intro hz
      obtain ⟨child,j,hj,hl,hcode⟩ := (hn z).mp hz
      exact ⟨child,t,⟨ht,j,hj,(hf.2 j child).mpr ⟨hj,hl⟩,
        (topPredicate_semantics t j t).mpr rfl⟩,hcode⟩
    · rintro ⟨child,p,⟨_,j,hj,hjf,hr⟩,hcode⟩
      have e := (topPredicate_semantics t j p).mp hr
      subst p
      exact (hn z).mpr ⟨child,j,hj,((hf.2 j child).mp hjf).2,hcode⟩

theorem exists_labelSet (hM : FirstOrder.Theory.Models M nativeZF)
    {W K c t : M.Carrier .set} (hc : FunctionOn K c)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t W) (I b : M.Carrier .set) :
    ∃ name, LabelSet (M := M) W I K c t b name := by
  obtain ⟨f,hf⟩ := exists_family hM hc W I t b
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM topPredicate (fun _ : Fin 1 => t) I f W
  exact ⟨name,(collected_iff hf ht).mp hn⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {W I K c t b a n : M.Carrier .set} (ha : LabelSet W I K c t b a) (hn : LabelSet W I K c t b n) : a = n :=
  (ModelTransfer.extensionality hM).eq_of_same_members a n (fun z => (ha z).trans (hn z).symm)

theorem edge_labelSet (hM : FirstOrder.Theory.Models M nativeZF)
    {W I K c t b name : M.Carrier .set} (hn : LabelSet W I K c t b name) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p name ↔ p = t ∧
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j I ∧ Label W K c t j b child := by
  constructor
  · rintro ⟨z,hcode,hz⟩
    obtain ⟨x,j,hj,hl,hcode'⟩ := (hn z).mp hz
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨rfl,j,hj,hl⟩
  · rintro ⟨hpt,j,hj,hl⟩
    subst p
    obtain ⟨z,hcode⟩ := KuratowskiZF.exists_code hM child t
    exact ⟨z,hcode,(hn z).mpr ⟨child,j,hj,hl,hcode⟩⟩

/-- The full label set is HS and literally fixed by the whole label group. -/
theorem HS_and_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w mu G F c t b name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hNormal : ForcingNormalFilter.Normal I G F)
    (hFilter : ForcingSupportFilter.Filter I G mu F)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hc : FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hn : LabelSet (v 6) I K c t b name) :
    ForcingHS.HS actionFormula v G (v 6) F name ∧ ForcingSupportedNames.Supported v G name := by
  obtain ⟨f,hf⟩ := exists_family hM hc (v 6) I t b
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  have hFamily : ForcingCollectedHS.FamilyHS v G (v 6) F I f := by
    intro j child hj hjc
    exact ForcingLabelNames.label_HS hM v hp hG hNormal hFilter hw hSmall hc ht hj
      ((hf.2 j child).mp hjc).2
  have hIndex : ForcingCollectedHS.IndexedPermutes topPredicate (fun _ : Fin 1 => t) v G I f (v 6) := by
    intro g hg A hga i child p hi hic _ htop
    have ep := (topPredicate_semantics t i p).mp htop
    subst p
    have hpi := (hG g).mp hg
    obtain ⟨j,hij,_⟩ := hpi.1.1.2 i hi
    have hj := hpi.1.2 i j hij
    obtain ⟨image,hji,_⟩ := hf.1.2 j hj
    have hAg := (mapRel_action v g A).mp hga
    exact ⟨j,image,t,hj,hji,(topPredicate_semantics t j t).mpr rfl,
      ForcingLabelNames.label_move hM v hp ht hpi hAg hij
        ((hf.2 i child).mp hic).2 ((hf.2 j image).mp hji).2,
      ForcingProductFamily.top_fixed hp ht hAg⟩
  have hperm := (ForcingCollectedHS.indexed_permutes_iff hM topPredicate (fun _ : Fin 1 => t) v G I f).mp hIndex
  have hSub := ForcingSupportFilter.top_subgroup hM hG
  have hCollected := (collected_iff hf htW).mpr hn
  exact ⟨ForcingCollectedHS.collect_HS hM topPredicate (fun _ : Fin 1 => t) v hp hG hNormal hSub
    hNormal.1 hFamily hperm hCollected,
    fun g hg A hA => ForcingCollectedHS.fixed hM topPredicate (fun _ : Fin 1 => t) v hp hG hSub
      hFamily hperm hCollected hg hA⟩

def existenceSentence : Source.Sentence :=
  ((Source.SetLanguage.functionOn (3 : Fin 6) 2).imp
    ((Formula.mem 4 0).imp (.ex (labelSet 0 1 2 3 4 5 6)))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hc ht
  obtain ⟨name,hn⟩ := exists_labelSet hM
    ((ForcingConditionGraphs.functionOn_semantics (M := M) env 2 3).mp hc) ht (env 1) (env 5)
  refine ⟨name,?_⟩
  apply (labelSet_semantics (M := M) (Fin.lastCases name env)
    (0 : Fin 6).castSucc (1 : Fin 6).castSucc (2 : Fin 6).castSucc
    (3 : Fin 6).castSucc (4 : Fin 6).castSucc (5 : Fin 6).castSucc (Fin.last 6)).mpr
  simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hn

theorem existence_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)

def uniquenessSentence : Source.Sentence :=
  ((labelSet (0 : Fin 8) 1 2 3 4 5 6).imp
    ((labelSet 0 1 2 3 4 5 7).imp (.equal 6 7))).close

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env ha hb
  exact unique hM ((labelSet_semantics (M := M) env 0 1 2 3 4 5 6).mp ha)
    ((labelSet_semantics (M := M) env 0 1 2 3 4 5 7).mp hb)

theorem uniqueness_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)

def result {k : Nat} (rho : Fin 7 → Fin k) (I K c t b G F : Fin k) : Formula k :=
  .ex ((labelSet (rho 6).castSucc I.castSucc K.castSucc c.castSucc t.castSucc b.castSucc (Fin.last k)).conj
    ((ForcingHS.hs actionFormula (fun i => (rho i).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
      (ForcingEquivariantMix.fixedAll (fun i => (rho i).castSucc) G.castSucc (Fin.last k))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K c t b G F : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho I K c t b G F) ↔
      ∃ name, LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) name ∧
        ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) name ∧
          ForcingSupportedNames.Supported (fun i => env (rho i)) (env G) name := by
  simp only [result,Formula.Realize,labelSet_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Actual set of all labels, with HS and full-group fixation; no given family. -/
def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
        (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
          (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
            (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
              (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
                (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
                  (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
                    (ProjectSyntax.encode id (result rho I K c t b G F))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t b : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w mu G F c t b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho I K B w mu G F c t b)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),result_semantics (M := M),Project.Term.eval_bound]
  intro hw hSmall hp hG hNormal hFilter hc ht
  have htW := (hp.2.2.2.2.2 (bound t)).mpr (Or.inl ht)
  obtain ⟨name,hn⟩ := exists_labelSet hM hc htW (bound I) (bound b)
  exact ⟨name,hn,HS_and_fixed hM (fun i => bound (rho i)) hp hG hNormal hFilter hw hSmall hc ht hn⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t b : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w mu G F c t b)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mu G F c t b hM)

end PPAC.Migration.ForcingLabelSet
