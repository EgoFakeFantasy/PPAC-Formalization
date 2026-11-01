/- Pinned ClassFibers.quotientName/mem_quotientName/quotientName_fixed.
The actual all-condition collection of canonical label classes; consumer:
AssignedGraphs.graphWitness_bounds and assignmentGraph_bijection. -/
import PPAC.Migration.ForcingRelationClassMove
import PPAC.Migration.ForcingLabelDensity

namespace PPAC.Migration.ForcingQuotientName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingStabilizer (Action)
open ForcingHS (HS)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingRelationClassMove (Value family family_semantics)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Family {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K c t b labels E : Fin k) (f : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn (env I) f ∧ ∀ i name,
    PureKuratowski.PairMember M i name f ↔ MapRel (family rho G F mul I K c t b labels E) env i name

def familyGraph {k m : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    (rr : Fin k → Fin m) (f : Fin m) : Formula m :=
  (Source.SetLanguage.functionOn f (rr I)).conj (.all (.all
    ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (rel (family rho G F mul I K c t b labels E) (paramsUp (paramsUp rr))
        (Fin.last m).castSucc (Fin.last (m+1))))))

theorem familyGraph_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) (rr : Fin k → Fin m) (f : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (familyGraph rho G F mul I K c t b labels E rr f) ↔
      Family (fun j => env (rr j)) rho G F mul I K c t b labels E (env f) := by
  simp only [familyGraph,Family,Source.Formula.iff,Formula.Realize,
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact and_congr Iff.rfl ⟨fun h i name => ⟨(h i name).1,(h i name).2⟩,
    fun h i name => ⟨(h i name).mp,(h i name).mpr⟩⟩

/-- Keep the existing native function constructors opaque at the concrete
class formula; this is only their Source-formula interface. -/
private theorem collect_family_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (query : Formula (k+2)) (env : Fin k → M.Carrier .set) (I : M.Carrier .set)
    (htotal : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∃ name, MapRel query env i name)
    (hu : ∀ i a b, MapRel query env i a → MapRel query env i b → a = b)
    (hd : ∀ i name, MapRel query env i name → (Project.FirstOrderSemantics.reduct M).mem i I) :
    ∃ f, ForcingConditionGraphs.FunctionOn I f ∧
      ∀ i name, PureKuratowski.PairMember M i name f ↔ MapRel query env i name := by
  let v : Env (Project.FirstOrderSemantics.reduct M) k :=
    { bound := fun i => env i.rev, free := fun _ => I }
  have hRel := fun i name => ForcingMapConditions.binary_semantics hM query env I i name
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I →
      ∃ name, (ProjectSyntax.binary query).denote v i name := by
    intro i hi
    obtain ⟨name,hn⟩ := htotal i hi
    exact ⟨name,(hRel i name).mpr hn⟩
  have huniq : ∀ i a b, (ProjectSyntax.binary query).denote v i a →
      (ProjectSyntax.binary query).denote v i b → a = b :=
    fun i a b ha hb => hu i a b ((hRel i a).mp ha) ((hRel i b).mp hb)
  obtain ⟨bound,hbound⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) v I ht huniq
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (ProjectSyntax.binary query) v (source := I) (target := bound) ht
    (fun i _ a b ha hb => huniq i a b ha hb)
    (fun i name hi hn => (hbound name).mpr ⟨i,hi,hn⟩)
  refine ⟨f,((ForcingSupportSize.native_mapsTo hM I bound f).mpr hf).1,?_⟩
  intro i name
  exact ⟨fun h => (hRel i name).mp ((he i name).mp h).2,
    fun h => (he i name).mpr ⟨hd i name h,(hRel i name).mpr h⟩⟩

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {B w mu : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (ht : ForcingWithTopCarrier.Empty (env t))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E)) :
    ∃ f, Family env rho G F mul I K c t b labels E f := by
  apply collect_family_graph hM (family rho G F mul I K c t b labels E) env (env I)
  · intro i hi
    obtain ⟨name,hn⟩ := ForcingRelationClassMove.value_exists hM env rho G F mul hp hG hF hw hMu hc ht hLabels hE hi

    exact ⟨name,(family_semantics env rho G F mul I K c t b labels E i name).mpr hn⟩
  · intro i x1 x2 hx1 hx2
    exact ForcingRelationClassMove.value_unique hM
      ((family_semantics env rho G F mul I K c t b labels E i x1).mp hx1)
      ((family_semantics env rho G F mul I K c t b labels E i x2).mp hx2)
  · intro i name h
    exact ((family_semantics env rho G F mul I K c t b labels E i name).mp h).1

/-- Source collect predicate is True at every condition, not only the top. -/
def allConditions {k : Nat} : Formula (k+2) := .imp .bot .bot

def Quotient {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K c t b labels E : Fin k) (name : M.Carrier .set) : Prop :=
  ∃ f, Family env rho G F mul I K c t b labels E f ∧
    ForcingCollectedName.Collected allConditions env (env I) f (env (rho 6)) name

def quotient {k m : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    (rr : Fin k → Fin m) (name : Fin m) : Formula m :=
  .ex ((familyGraph rho G F mul I K c t b labels E (paramsUp rr) (Fin.last m)).conj
    (ForcingCollectedName.collected allConditions (paramsUp rr) (rr I).castSucc (Fin.last m)
      (rr (rho 6)).castSucc name.castSucc))

theorem quotient_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) (rr : Fin k → Fin m) (name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (quotient rho G F mul I K c t b labels E rr name) ↔
      Quotient (fun j => env (rr j)) rho G F mul I K c t b labels E (env name) := by
  simp only [quotient,Quotient,Formula.Realize,familyGraph_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {B w mu : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (ht : ForcingWithTopCarrier.Empty (env t))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E)) :
    ∃ name, Quotient env rho G F mul I K c t b labels E name := by
  obtain ⟨f,hf⟩ := exists_family hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hE
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM allConditions env (env I) f (env (rho 6))
  exact ⟨name,f,hf,hn⟩

theorem mem_quotient (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {name y p : M.Carrier .set}
    (hn : Quotient env rho G F mul I K c t b labels E name)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p → ∃ r i cls,
          (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
          MapRel (orderFormula (rho 0) mul) env r q ∧
          MapRel (family rho G F mul I K c t b labels E) env i cls ∧
          Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y cls r := by
  obtain ⟨f,hf,hn⟩ := hn
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · intro h q hq hqp
    obtain ⟨r,cls,d,hr,hrq,_,he,_,heq⟩ := h.2 q hq hqp
    obtain ⟨_,i,_,hic,_⟩ := (ForcingCollectedName.edge_collected hM hn cls d).mp he
    exact ⟨r,i,cls,hr,hrq,(hf.2 i cls).mp hic,heq⟩
  · intro h
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,i,cls,hr,hrq,hic,heq⟩ := h q hq hqp
    exact ⟨r,cls,r,hr,hrq,hr,(ForcingCollectedName.edge_collected hM hn cls r).mpr
      ⟨hr,i,((family_semantics env rho G F mul I K c t b labels E i cls).mp hic).1,
        (hf.2 i cls).mpr hic,fun h => h⟩,hpre.1 r hr,heq⟩

theorem hs_and_fixed (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {B w mu name : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (ht : ForcingWithTopCarrier.Empty (env t))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hn : Quotient env rho G F mul I K c t b labels E name) :
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ∀ g, (Project.FirstOrderSemantics.reduct M).mem g (env G) → ∀ a,
        MapRel actionFormula (fun j => env (rho j)) g a →
        Action (env (rho 6)) a (env E) (env E) → Action (env (rho 6)) a name name := by
  obtain ⟨f,hf,hn⟩ := hn
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  obtain ⟨S,hS,hSF,hFix⟩ := ForcingTupleStabilizer.exists_tuple hM (fun j => env (rho j))
    hp hG hNormal (fun _ : Fin 1 => env E) (fun _ => hE)
  have hfamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j))
      (env G) (env (rho 6)) (env F) (env I) f := by
    intro i child _ hic
    exact ((family_semantics env rho G F mul I K c t b labels E i child).mp ((hf.2 i child).mp hic)).2.1
  have hperm : ForcingCollectedHS.Permutes allConditions env (fun j => env (rho j)) S (env I) f (env (rho 6)) := by
    intro g hg a hga child p image q had hmove hpq
    obtain ⟨_,i,hi,hic,_⟩ := had
    have hpi := (hG g).mp (hS.1 g hg)
    obtain ⟨j,hij,_⟩ := hpi.1.1.2 i hi
    have hj := hpi.1.2 i j hij
    obtain ⟨nj,hjn,_⟩ := hf.1.2 j hj
    have hEE := ForcingTupleStabilizer.fixed_action hM hFix hg hga (0 : Fin 1)
    have hm := ForcingRelationClassMove.labelClass_move hM env rho G F mul hp hG hF hw hMu hc ht hLabels
      hpi hga hEE hij
      ((family_semantics env rho G F mul I K c t b labels E i child).mp ((hf.2 i child).mp hic))
      ((family_semantics env rho G F mul I K c t b labels E j nj).mp ((hf.2 j nj).mp hjn))
    have har := ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)
    have he := ForcingNameConjugacy.unique hM har.1 hm hmove
    subst nj
    exact ⟨har.1.2 p q hpq,j,hj,hjn,fun h => h⟩
  refine ⟨ForcingCollectedHS.collect_HS hM allConditions env (fun j => env (rho j))
    hp hG hNormal hS hSF hfamily hperm hn,?_⟩
  intro g hg a hga hEE
  exact ForcingCollectedHS.fixed hM allConditions env (fun j => env (rho j)) hp hG hS hfamily hperm hn
    ((hFix g).mpr ⟨hg,fun _ => ⟨a,hga,hEE⟩⟩) hga

/-- Exact source isClass predicate, for every internal HS name and condition. -/
theorem mem_quotient_iff_isClass (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {B w mu name y p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (ht : ForcingWithTopCarrier.Empty (env t))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hn : Quotient env rho G F mul I K c t b labels E name)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name p ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 y (env labels) (env E))
        (env (rho 6)) p (ForcingEligibility.isClass 0 1 2) := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  obtain ⟨hA,_⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels
  have htW := (hp.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env t) := by
    intro q _
    exact (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q (env t)).mpr (Or.inl ht)
  rw [mem_quotient hM env rho G F mul I K c t b labels E hn hpre hpW,
    ForcingRelationClass.forces_isClass hM env rho G F mul hp hG hNormal hpre hpW
      (args3 y (env labels) (env E)) 0 1 2 hy hA hE]
  constructor
  · intro hd q hq hqp
    obtain ⟨r,i,cls,hr,hrq,hval,heq⟩ := hd q hq hqp
    obtain ⟨hi,hcls,x,hx,hclass⟩ := (family_semantics env rho G F mul I K c t b labels E i cls).mp hval
    have hxHS := ForcingLabelNames.label_HS hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hi hx
    refine ⟨r,hr,hrq,x,cls,hxHS,hcls,hclass,?_,heq⟩
    apply (ForcingLabelDensity.mem_labelSet hM _ env hLabels hr htW hTop).mpr
    intro s hs _
    exact ⟨s,i,x,hs,hpre.1 s hs,hi,hx,ForcingAtomicBasic.eq_refl hM hpre x s hs⟩
  · intro hd q hq hqp
    obtain ⟨r,hr,hrq,x,old,_,hold,hclass,hm,heq⟩ := hd q hq hqp
    obtain ⟨s,i,x',hs,hsr,hi,hx',hxx'⟩ :=
      (ForcingLabelDensity.mem_labelSet hM _ env hLabels hr htW hTop).mp hm r hr (hpre.1 r hr)
    obtain ⟨f,hf,_⟩ := hn
    obtain ⟨cls,hic,_⟩ := hf.1.2 i hi
    have hval := (hf.2 i cls).mp hic
    obtain ⟨_,hcls,x'',hx'',hclass'⟩ := (family_semantics env rho G F mul I K c t b labels E i cls).mp hval
    have he := ForcingLabelNames.unique hM hx'' hx'
    subst x''
    refine ⟨s,i,cls,hs,hpre.2 s r q hs hr hq hsr hrq,hval,?_⟩
    exact ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hs hsr heq)
      (ForcingRelationClass.congr hM hpre hold hcls hclass hclass' hs
        (ForcingAtomicBasic.eq_refl hM hpre (env labels) s hs)
        (ForcingAtomicBasic.eq_refl hM hpre (env E) s hs) hxx')

def constructionResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) : Formula k :=
  .ex ((quotient rho G F mul I K c t b labels E (paramsUp id) (Fin.last k)).conj
    (ForcingHS.hs actionFormula (paramsUp rho) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)))

theorem constructionResult_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (constructionResult rho G F mul I K c t b labels E) ↔
      ∃ name, Quotient env rho G F mul I K c t b labels E name ∧
        HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name := by
  simp only [constructionResult,Formula.Realize,quotient_semantics (M := M),ForcingHS.hs_semantics (M := M),
    paramsUp,id_eq,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Shared background only; no supplied quotient, function family or support. -/
private def backgroundSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t b labels E : Fin k) (result : Formula k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels))
      (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
        (ProjectSyntax.encode id result))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed]

private theorem background_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t b labels E : Fin k) (result : Formula k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (h : ∀ env : Fin k → M.Carrier .set,
      (Project.FirstOrderSemantics.reduct M).IsOmega (env w) →
      (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu) →
      Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
        (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) →
      ForcingLabelPermutations.Carrier (env I) (env G) →
      ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F) →
      ForcingConditionGraphs.FunctionOn (env K) (env c) → ForcingWithTopCarrier.Empty (env t) →
      ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels) →
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E) →
      Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env result) :
    (Project.fo_sentence (backgroundSentence rho I K B w mu G F c t b labels E result)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (backgroundSentence rho I K B w mu G F c t b labels E result)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingHS.hs_semantics (M := M)]
  exact h env

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E : Fin k) : Project.Sentence :=
  backgroundSentence rho I K B w mu G F c t b labels E (constructionResult rho G F mul I K c t b labels E)

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w mu G F mul c t b labels E)).TrueIn M := by
  apply background_models
  intro env hw hMu hp hG hF hc ht hLabels hE
  apply (constructionResult_semantics env rho G F mul I K c t b labels E).mpr
  obtain ⟨name,hn⟩ := exists_quotient hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hE
  exact ⟨name,hn,(hs_and_fixed hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hE hn).1⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w mu G F mul c t b labels E)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mu G F mul c t b labels E hM)

def lawsResult {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K c t b labels E name g a y p : Fin k) : Formula k :=
  (quotient rho G F mul I K c t b labels E id name).imp
    (((Formula.mem g G).imp ((rel actionFormula rho g a).imp
      ((ForcingStabilizer.action (rho 6) a E E).imp (ForcingStabilizer.action (rho 6) a name name)))).conj
    ((ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp
      ((ForcingHS.hs actionFormula rho G (rho 6) F y).imp ((Formula.mem p (rho 6)).imp
        ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) y name p).iff
          (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 y labels E)
            (rho 6) p (ForcingEligibility.isClass 0 1 2)))))))

theorem lawsResult_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K c t b labels E name g a y p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (lawsResult rho G F mul I K c t b labels E name g a y p) ↔
      (Quotient env rho G F mul I K c t b labels E (env name) →
        ((Project.FirstOrderSemantics.reduct M).mem (env g) (env G) →
          MapRel actionFormula (fun j => env (rho j)) (env g) (env a) →
          Action (env (rho 6)) (env a) (env E) (env E) → Action (env (rho 6)) (env a) (env name) (env name)) ∧
        (ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)) →
          HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env y) →
          (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)) →
          (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (env y) (env name) (env p) ↔
            Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env y) (env labels) (env E))
              (env (rho 6)) (env p) (ForcingEligibility.isClass 0 1 2)))) := by
  simp only [lawsResult,Source.Formula.iff,Formula.Realize,quotient_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingStabilizer.action_semantics (M := M),
    ForcingAtomicBasic.preorder_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingFormula.formula_semantics (M := M),id_eq]
  have hargs : (fun j => env (args3 y labels E j)) = args3 (env y) (env labels) (env E) := by
    funext j
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.elim0 j) j) j) j
  rw [hargs]
  exact forall_congr' (fun _ => and_congr Iff.rfl (forall_congr' (fun _ =>
    forall_congr' (fun _ => forall_congr' (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)))))

def lawsSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E name g a y p : Fin k) : Project.Sentence :=
  backgroundSentence rho I K B w mu G F c t b labels E (lawsResult rho G F mul I K c t b labels E name g a y p)

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E name g a y p : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (lawsSentence rho I K B w mu G F mul c t b labels E name g a y p)).TrueIn M := by
  apply background_models
  intro env hw hMu hp hG hF hc ht hLabels hE
  apply (lawsResult_semantics env rho G F mul I K c t b labels E name g a y p).mpr
  intro hn
  refine ⟨fun hg ha he => (hs_and_fixed hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hE hn).2 (env g) hg (env a) ha he,?_⟩
  intro hpre hy hpW
  exact mem_quotient_iff_isClass hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hE hn hy hpre hpW

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F mul c t b labels E name g a y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (lawsSentence rho I K B w mu G F mul c t b labels E name g a y p)) :=
  ModelTransfer.derives (fun _ hM => laws_models rho I K B w mu G F mul c t b labels E name g a y p hM)

end PPAC.Migration.ForcingQuotientName
