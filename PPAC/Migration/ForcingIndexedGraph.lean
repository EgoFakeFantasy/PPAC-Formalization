/- Pinned Models/GraphFusion.indexedGraph:16-93. Actual internal graph of
the uniformly supported name family, using the existing check/opair/collect
constructors. Preserve literal entries and the full functionOn formula.
No external name family, rank cutoff or new recursion/choice backend. -/
import PPAC.Migration.ForcingSupportedNames
import PPAC.Migration.ForcingPairFormula
import PPAC.Migration.ForcingCheckReflection
import PPAC.Migration.ForcingLabelNames

namespace PPAC.Migration.ForcingIndexedGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingConditionGraphs (FunctionOn)
open ForcingCheckName (Checked)
open ForcingOrderedPairName (OrderedPairName)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingSupportedNames (Supported)
open ForcingStabilizer (Action)
open ForcingMapConditions (MapRel)
open ForcingHS (HS)
open Source.SetLanguage (args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1400000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def PairValue (t f i pair : M.Carrier .set) : Prop :=
  ∃ checked nu, Checked t i checked ∧ PureKuratowski.PairMember M i nu f ∧ OrderedPairName t checked nu pair

def pairValue {n : Nat} (t f i pair : Fin n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName t.succ.succ i.succ.succ 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ i.succ.succ 0))
      (ProjectSyntax.encode id (ForcingOrderedPairName.orderedPairName t.succ.succ 1 0 pair.succ.succ)))))

theorem pairValue_freeClosed {n : Nat} (t f i pair : Fin n) : (pairValue t f i pair).FreeClosed := by
  simp -implicitDefEqProofs [pairValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem pairValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (t f i pair : Fin n) :
    Project.Formula.satisfies env (pairValue t f i pair) ↔
      PairValue (env.bound t) (env.bound f) (env.bound i) (env.bound pair) := by
  simp only [pairValue,PairValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCheckName.checkName_semantics (M := M),KuratowskiZF.source_edge,
    ForcingOrderedPairName.orderedPairName_semantics (M := M)]
  rfl

private theorem pairValue_unique (hM : FirstOrder.Theory.Models M nativeZF) {X t f i a b : M.Carrier .set}
    (hf : FunctionOn X f) (ha : PairValue t f i a) (hb : PairValue t f i b) : a = b := by
  obtain ⟨ci,nu,hci,hnu,ha⟩ := ha
  obtain ⟨ci',nu',hci',hnu',hb⟩ := hb
  have ec := ForcingCheckName.unique hM hci' hci
  have en := ForcingConditionGraphs.function_unique hf hnu' hnu
  subst ci'; subst nu'
  exact ForcingOrderedPairName.unique hM ha hb

def PairFamily (X t f pairs : M.Carrier .set) : Prop :=
  FunctionOn X pairs ∧ ∀ i pair, PureKuratowski.PairMember M i pair pairs → PairValue t f i pair

/-- Both the check-name and ordered-pair witnesses are actually constructed.
Native Collection provides a bound; uniqueness builds the internal function. -/
theorem exists_pairFamily (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (t f : Fin k) (X : M.Carrier .set) (hf : FunctionOn X (env f)) :
    ∃ pairs, PairFamily X (env t) (env f) pairs := by
  let schema : Project.BinarySchema k := {body := pairValue t.succ.succ f.succ.succ 1 0,freeClosed := pairValue_freeClosed ..}
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env t⟩
  have he i pair : schema.denote penv i pair ↔ PairValue (env t) (env f) i pair := pairValue_semantics hM _ _ _ _ _
  have hTotal i (hi : (Project.FirstOrderSemantics.reduct M).mem i X) : ∃ pair, schema.denote penv i pair := by
    obtain ⟨nu,hnu,_⟩ := hf.2 i hi
    obtain ⟨ci,hci⟩ := ForcingCheckName.exists_checked hM (env t) i
    obtain ⟨pair,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env t) ci nu
    exact ⟨pair,(he i pair).mpr ⟨ci,nu,hci,hnu,hPair⟩⟩
  obtain ⟨bound,hBound⟩ := ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM) schema penv X hTotal
  obtain ⟨pairs,hPairs,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema penv (source := X) (target := bound)
    (fun i hi => by obtain ⟨p,_,hp⟩ := hBound i hi; exact ⟨p,hp⟩)
    (fun _ _ _ _ ha hb => pairValue_unique hM hf ((he _ _).mp ha) ((he _ _).mp hb))
    (fun i p hi hp => by
      obtain ⟨p',hp',hVal⟩ := hBound i hi
      have eq := pairValue_unique hM hf ((he i p).mp hp) ((he i p').mp hVal)
      exact eq.symm ▸ hp')
  exact ⟨pairs,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hPairs).1,
    fun i pair hi => (he i pair).mp ((hEdge i pair).mp hi).2⟩

def collectTest : Formula 2 := .equal 0 0

private theorem collectTest_true (i p : M.Carrier .set) : MapRel collectTest Fin.elim0 i p := by
  rfl

def Graph (P X t f name : M.Carrier .set) : Prop :=
  ∀ child p, PureKuratowski.PairMember M child p name ↔
    (Project.FirstOrderSemantics.reduct M).mem p P ∧ ∃ i,
      (Project.FirstOrderSemantics.reduct M).mem i X ∧ PairValue t f i child

/-- Literal source collectRaw graph; the selected family and collector are
actual outputs, not hypothetical inputs to the existence conclusion. -/
theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (P t f : Fin k) (X : M.Carrier .set) (hf : FunctionOn X (env f)) :
    ∃ pairs name, PairFamily X (env t) (env f) pairs ∧
      ForcingCollectedName.Collected collectTest Fin.elim0 X pairs (env P) name ∧ Graph (env P) X (env t) (env f) name := by
  obtain ⟨pairs,hPairs⟩ := exists_pairFamily hM env t f X hf
  obtain ⟨name,hName⟩ := ForcingCollectedName.exists_collected hM collectTest Fin.elim0 X pairs (env P)
  refine ⟨pairs,name,hPairs,hName,?_⟩
  intro child p
  rw [ForcingCollectedName.edge_collected hM hName child p]
  constructor
  · rintro ⟨hp,i,hi,hip,_⟩
    exact ⟨hp,i,hi,hPairs.2 i child hip⟩
  · rintro ⟨hp,i,hi,hVal⟩
    obtain ⟨pair,hip,_⟩ := hPairs.1.2 i hi
    have eq := pairValue_unique hM hf hVal (hPairs.2 i pair hip)
    exact ⟨hp,i,hi,eq.symm ▸ hip,collectTest_true i p⟩

private theorem pair_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w t pi act ci nu pair : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (ht : ForcingWithTopCarrier.Empty t)
    (ha : ForcingProductFamily.Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi act)
    (hc : Action (v 6) act ci ci) (hnu : Action (v 6) act nu nu)
    (hPair : OrderedPairName t ci nu pair) : Action (v 6) act pair pair := by
  have hPerm := ForcingProductFamily.action_permutation ha
  obtain ⟨image,hImage⟩ := ForcingNameConjugacy.exists_action hM hPerm.1 pair
  let params := args2 (v 6) act
  have hTop : ForcingConditionAction.Act (v 6) act t t :=
    Or.inl ⟨(hp.2.2.2.2.2 t).mpr (Or.inl ht),ForcingProductFamily.top_fixed hp ht ha⟩
  have hMapped := ForcingOrderedPairName.map_orderedPairName hM
    (ForcingConditionAction.act_function params (0 : Fin 2) 1 hPerm.1) hPair
    ((ForcingConditionAction.relation_semantics params (0 : Fin 2) 1 t t).mpr hTop)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 ci ci).mpr hc)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 nu nu).mpr hnu)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 pair image).mpr hImage)
  exact (ForcingOrderedPairName.unique hM hMapped hPair) ▸ hImage

/-- Source indexedGraph's HS and exact supplied common support. -/
theorem hs_and_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H X t f pairs name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H) (hHF : (Project.FirstOrderSemantics.reduct M).mem H F)
    (ht : ForcingWithTopCarrier.Empty t)
    (hFamily : ForcingCollectedHS.FamilyHS v G (v 6) F X f)
    (hFixed : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i X → PureKuratowski.PairMember M i nu f → Supported v H nu)
    (hPairs : PairFamily X t f pairs)
    (hName : ForcingCollectedName.Collected collectTest Fin.elim0 X pairs (v 6) name) :
    HS actionFormula v G (v 6) F name ∧ Supported v H name := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  have hCheck x checked (hc : Checked t x checked) : HS actionFormula v G (v 6) F checked := by
    apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x checked hc
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ha⟩⟩
  have hPairHS : ForcingCollectedHS.FamilyHS v G (v 6) F X pairs := by
    intro i pair hi hip
    obtain ⟨ci,nu,hci,hif,hPair⟩ := hPairs.2 i pair hip
    exact ForcingOrderedPairName.orderedPair_hs hM v hp hG hF ht (hCheck i ci hci) (hFamily i nu hi hif) hPair
  have hPerm : ForcingCollectedHS.Permutes collectTest Fin.elim0 v H X pairs (v 6) := by
    intro pi hpi act hAct child p image q hAd hImage hpq
    obtain ⟨hpP,i,hi,hip,_⟩ := hAd
    obtain ⟨ci,nu,hci,hif,hPair⟩ := hPairs.2 i child hip
    have ha := (mapRel_action v pi act).mp hAct
    have hFixedPair := pair_fixed hM v hp ht ha (ForcingLabelNames.checked_fixed hM v hp ht ha hci)
      (hFixed i nu hi hif pi hpi act hAct) hPair
    have eq := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation ha).1 hImage hFixedPair
    subst image
    exact ⟨(ForcingProductFamily.action_permutation ha).1.2 p q hpq,i,hi,hip,collectTest_true i q⟩
  exact ⟨ForcingCollectedHS.collect_HS hM collectTest Fin.elim0 v hp hG hF hH hHF hPairHS hPerm hName,
    fun pi hpi act hAct => ForcingCollectedHS.fixed hM collectTest Fin.elim0 v hp hG hH hPairHS hPerm hName hpi hAct⟩

private theorem checked_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t x checked : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t) (hc : Checked t x checked) : HS actionFormula v G (v 6) F checked := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x checked hc
  intro pi hpi
  obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG pi).mp hpi)
  exact ⟨act,(mapRel_action v pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
    Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ha⟩⟩

def MemValue {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (P X t f nu p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i X ∧
        ∃ pair, PairValue t f i pair ∧ Forces true R env P nu pair r

/-- Complete source mem_indexedGraph, for every internal name and condition. -/
theorem mem_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {P X t f name nu p : M.Carrier .set}
    (ht : (Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    (hGraph : Graph P X t f name) (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔ MemValue R env P X t f nu p := by
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · rintro ⟨_,h⟩ q hq hqp
    obtain ⟨r,child,c,hr,hrq,_,hc,_,he⟩ := h q hq hqp
    obtain ⟨_,i,hi,hPair⟩ := (hGraph child c).mp hc
    exact ⟨r,hr,hrq,i,hi,child,hPair,he⟩
  · intro h
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi,pair,hPair,he⟩ := h q hq hqp
    exact ⟨r,pair,t,hr,hrq,ht,(hGraph pair t).mpr ⟨ht,i,hi,hPair⟩,htop r hr,he⟩

def AppValue {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (P X t f x y p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i X ∧ ∃ ci nu,
        Checked t i ci ∧ PureKuratowski.PairMember M i nu f ∧ Forces true R env P x ci r ∧ Forces true R env P y nu r

/-- Complete source app_indexedGraph, retaining both forced equalities. -/
theorem app_graph (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul t : Fin k)
    (v : Fin m → M.Carrier .set) (graph x y : Fin m) {I K B w X f p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hGraph : Graph (env (rho 6)) X (env t) f (v graph))
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v x))
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v y))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.edge graph x y) ↔
      AppValue (orderFormula (rho 0) mul) env (env (rho 6)) X (env t) f (v x) (v y) p := by
  have htW := (hPres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r (env t) :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r (env t)).mpr (Or.inl ht)
  obtain ⟨pair,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env t) (v x) (v y)
  rw [ForcingPairFormula.app_iff_mem_opair hM env rho G F mul v graph x y hPres hG hF ht hpre hx hy hPair hp]
  rw [mem_graph hM htW htop hGraph hp]
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,i,hi,pair',⟨ci,nu,hci,hif,hPair'⟩,he⟩ := h q hq hqp
    obtain ⟨hx,hy⟩ := (ForcingOrderedPairForcing.eq_opair_iff hM hpre htW htop hPair hPair').mp he
    exact ⟨r,hr,hrq,i,hi,ci,nu,hci,hif,hx,hy⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,i,hi,ci,nu,hci,hif,hx,hy⟩ := h q hq hqp
    obtain ⟨pair',hPair'⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env t) ci nu
    exact ⟨r,hr,hrq,i,hi,pair',⟨ci,nu,hci,hif,hPair'⟩,
      ForcingOrderedPairForcing.eq_opair_congr hM hpre htW htop hPair hPair' hx hy⟩

theorem app_at (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul t : Fin k)
    {I K B w X f graph i ci nu p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hGraph : Graph (env (rho 6)) X (env t) f graph)
    (hFamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X f)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i X) (hci : Checked (env t) i ci)
    (hif : PureKuratowski.PairMember M i nu f) (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph ci nu) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) := by
  apply (app_graph hM env rho G F mul t (args3 graph ci nu) 0 1 2 hPres hG hF ht hpre hGraph
    (checked_hs hM (fun j => env (rho j)) hPres hG hF ht hci) (hFamily i nu hi hif) hp).mpr
  intro q hq _
  exact ⟨q,hq,hpre.1 q hq,i,hi,ci,nu,hci,hif,ForcingAtomicBasic.eq_refl hM hpre ci q hq,
    ForcingAtomicBasic.eq_refl hM hpre nu q hq⟩

/-- Full source indexedGraph_functionOn, including every graph member's
ordered-pair shape and the unique value for each member of check(X). -/
theorem functionOn (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul t : Fin k)
    (v : Fin m → M.Carrier .set) (graph d : Fin m) {I K B w X f p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hf : FunctionOn X f) (hChecked : Checked (env t) X (v d))
    (hFamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X f)
    (hGraph : Graph (env (rho 6)) X (env t) f (v graph))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.functionOn graph d) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 2 → M.Carrier .set := fun j => v (args2 graph d j)
  have htW := (hPres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r (env t) :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r (env t)).mpr (Or.inl ht)
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  constructor
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro nu hnu
    have hNuHS := (domain_semantics env rho G F nu).mp hnu
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq _ hMem
    change Forces false R env W nu (v graph) q at hMem
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨s,hs,hsr,i,hi,pair,⟨ci,value,hci,hif,hPair⟩,he⟩ := (mem_graph hM htW htop hGraph hq).mp hMem r hr hrq
    have hCiHS := checked_hs hM (fun j => env (rho j)) hPres hG hF ht hci
    have hValueHS := hFamily i value hi hif
    refine ⟨s,hs,hsr,ci,(domain_semantics env rho G F ci).mpr hCiHS,?_⟩
    apply (ForcingFormula.force_ex R H env _ W s _).mpr
    intro u hu hus
    let vv : Fin 5 → M.Carrier .set := Fin.lastCases value (Fin.lastCases ci (Fin.lastCases nu v0))
    refine ⟨u,hu,hpre.1 u hu,value,(domain_semantics env rho G F value).mpr hValueHS,?_,?_⟩
    · change Forces false R env W ci (v d) u
      exact ForcingInfinity.check_mem_of_mem hM hpre hChecked hci hi htW htop hu
    · exact (ForcingPairFormula.forces_orderedPair hM env rho G F mul vv (2 : Fin 5) 3 4
        hPres hG hF ht hpre hNuHS hCiHS hValueHS hPair hu).mpr (ForcingAtomicBasic.eq_mono hM hpre hu hus he)
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro x hx
    have hxHS := (domain_semantics env rho G F x).mp hx
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq _ hMem
    change Forces false R env W x (v d) q at hMem
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨s,hs,hsr,i,hi,ci,hci,hEqX⟩ := (ForcingInfinity.mem_check hM hChecked htW htop hq).mp hMem r hr hrq
    obtain ⟨value,hif,_⟩ := hf.2 i hi
    have hValueHS := hFamily i value hi hif
    let vv : Fin 4 → M.Carrier .set := Fin.lastCases value (Fin.lastCases x v0)
    refine ⟨s,hs,hsr,value,(domain_semantics env rho G F value).mpr hValueHS,?_,?_⟩
    · apply (app_graph hM env rho G F mul t vv (0 : Fin 4) 2 3 hPres hG hF ht hpre hGraph hxHS hValueHS hs).mpr
      intro u hu hus
      exact ⟨u,hu,hpre.1 u hu,i,hi,ci,value,hci,hif,ForcingAtomicBasic.eq_mono hM hpre hu hus hEqX,
        ForcingAtomicBasic.eq_refl hM hpre value u hu⟩
    · apply (ForcingFormula.force_all hM hpre hs _ _).mpr
      intro z hz
      have hzHS := (domain_semantics env rho G F z).mp hz
      let vz : Fin 5 → M.Carrier .set := Fin.lastCases z vv
      apply (ForcingFormula.force_imp hM hpre hs _ _ _).mpr
      intro u hu hus hApp
      apply ForcingAtomicBasic.eq_of_dense hM hpre hu
      intro a ha hau
      obtain ⟨b,hb,hba,j,hj,cj,value',hcj,hjf,hEqX',hEqZ⟩ :=
        (app_graph hM env rho G F mul t vz (0 : Fin 5) 2 4 hPres hG hF ht hpre hGraph hxHS hzHS hu).mp hApp a ha hau
      have hbs := hpre.2 b a s hb ha hs hba (hpre.2 a u s ha hu hs hau hus)
      have hEqChecks := ForcingAtomicLaws.eq_trans hM hpre
        (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hb hbs hEqX)) hEqX'
      have hij := (ForcingCheckReflection.eq_check_iff hM hpre htW htop hb hci hcj).mp hEqChecks
      subst j
      have eq := ForcingConditionGraphs.function_unique hf hjf hif
      exact ⟨b,hb,hba,eq ▸ hEqZ⟩

def graphFormula {n : Nat} (P X t f name : Fin n) : Project.Formula 1 n :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge name.succ.succ 1 0))
    (.conj (.mem (.bound 0) (.bound P.succ.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound X.succ.succ.succ))
        (pairValue t.succ.succ.succ f.succ.succ.succ 0 2))))))

theorem graphFormula_freeClosed {n : Nat} (P X t f name : Fin n) : (graphFormula P X t f name).FreeClosed := by
  simp -implicitDefEqProofs [graphFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,pairValue_freeClosed]

theorem graphFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (P X t f name : Fin n) :
    Project.Formula.satisfies env (graphFormula P X t f name) ↔
      Graph (env.bound P) (env.bound X) (env.bound t) (env.bound f) (env.bound name) := by
  simp only [graphFormula,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,pairValue_semantics hM]
  rfl

def fixedFamily {n : Nat} (rho : Fin 7 → Fin n) (H X f : Fin n) : Project.Formula 1 n :=
  .forallE (.imp (.mem (.bound 0) (.bound X.succ)) (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0))
      (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (rho j).succ.succ) H.succ.succ 0)))))

theorem fixedFamily_freeClosed {n : Nat} (rho : Fin 7 → Fin n) (H X f : Fin n) :
    (fixedFamily rho H X f).FreeClosed := by
  simp -implicitDefEqProofs [fixedFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem fixedFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin n) (H X f : Fin n) :
    Project.Formula.satisfies env (fixedFamily rho H X f) ↔
      ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i (env.bound X) → PureKuratowski.PairMember M i nu (env.bound f) →
        Supported (fun j => env.bound (rho j)) (env.bound H) nu := by
  simp only [fixedFamily,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingSupportedNames.supported_semantics (M := M)]
  constructor
  · intro h i nu hi hinu
    exact h i hi nu hinu
  · intro h i hi nu hinu
    exact h i nu hi hinu

def memValue {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f nu p : Fin m) : Project.Formula 1 m :=
  let up2 : Fin m → Fin (m+2) := fun j => j.succ.succ
  let up4 : Fin m → Fin (m+4) := fun j => j.succ.succ.succ.succ
  .forallE (.imp (.mem (.bound 0) (.bound P.succ))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun j => (base j).succ) 0 p.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound (up2 P)))
        (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun j => up2 (base j)) 0 1))
          (.existsE (.conj (.mem (.bound 0) (.bound X.succ.succ.succ))
            (.existsE (.conj (pairValue (up4 t) (up4 f) 1 0)
              (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun j => up4 (base j)) (up4 P) (up4 nu) 0 2)))))))))))

theorem memValue_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f nu p : Fin m) :
    (memValue R base P X t f nu p).FreeClosed := by
  simp -implicitDefEqProofs [memValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,pairValue_freeClosed]

theorem memValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f nu p : Fin m) :
    Project.Formula.satisfies env (memValue R base P X t f nu p) ↔
      MemValue R (fun j => env.bound (base j)) (env.bound P) (env.bound X) (env.bound t) (env.bound f) (env.bound nu) (env.bound p) := by
  simp only [memValue,MemValue,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingMapConditions.rel_semantics (M := M),pairValue_semantics hM,ForcingAtomicRelations.forces_semantics (M := M)]
  rfl

def appValue {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f x y p : Fin m) : Project.Formula 1 m :=
  let up2 : Fin m → Fin (m+2) := fun j => j.succ.succ
  let up5 : Fin m → Fin (m+5) := fun j => j.succ.succ.succ.succ.succ
  .forallE (.imp (.mem (.bound 0) (.bound P.succ))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun j => (base j).succ) 0 p.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound (up2 P)))
        (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel R (fun j => up2 (base j)) 0 1))
          (.existsE (.conj (.mem (.bound 0) (.bound X.succ.succ.succ))
            (.existsE (.existsE
              (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (up5 t) 2 1))
                (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up5 f) 2 0))
                  (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun j => up5 (base j)) (up5 P) (up5 x) 1 3))
                    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R (fun j => up5 (base j)) (up5 P) (up5 y) 0 3))))))))))))))

theorem appValue_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f x y p : Fin m) :
    (appValue R base P X t f x y p).FreeClosed := by
  simp -implicitDefEqProofs [appValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem appValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m) (P X t f x y p : Fin m) :
    Project.Formula.satisfies env (appValue R base P X t f x y p) ↔
      AppValue R (fun j => env.bound (base j)) (env.bound P) (env.bound X) (env.bound t) (env.bound f)
        (env.bound x) (env.bound y) (env.bound p) := by
  simp only [appValue,AppValue,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingMapConditions.rel_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics (M := M)]
  rfl

private theorem args2_map {a : Type v1} {b : Type v2} (e : a → b) (x y : a) :
    (fun j => e (args2 x y j)) = args2 (e x) (e y) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j <;> rfl

private theorem args3_map {a : Type v1} {b : Type v2} (e : a → b) (x y z : a) :
    (fun j => e (args3 x y z j)) = args3 (e x) (e y) (e z) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j <;> rfl

def Result {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → M.Carrier .set) (G F support X t f graph checkedX : M.Carrier .set) : Prop :=
  Graph (rho 6) X t f graph ∧ HS actionFormula rho G (rho 6) F graph ∧ Supported rho support graph ∧
    Checked t X checkedX ∧ ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (rho 6) →
      Force R Hdom env (args2 graph checkedX) (rho 6) p (Source.SetLanguage.functionOn 0 1) ∧
      (∀ nu, Forces false R env (rho 6) nu graph p ↔ MemValue R env (rho 6) X t f nu p) ∧
      ∀ x, HS actionFormula rho G (rho 6) F x → ∀ y, HS actionFormula rho G (rho 6) F y →
        (Force R Hdom env (args3 graph x y) (rho 6) p (Source.SetLanguage.edge 0 1 2) ↔ AppValue R env (rho 6) X t f x y p)

def resultFormula {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F support X t f graph checkedX : Fin m) : Project.Formula 1 m :=
  let up2 : Fin m → Fin (m+2) := fun j => j.succ.succ
  let up3 : Fin m → Fin (m+3) := fun j => j.succ.succ.succ
  let body : Project.Formula 1 (m+1) :=
    .conj (ProjectSyntax.encode id (ForcingFormula.formula R Hdom (fun j => (base j).succ)
      (args2 graph.succ checkedX.succ) (rho 6).succ 0 (Source.SetLanguage.functionOn 0 1)))
      (.conj
        (.forallE (.iff (ProjectSyntax.encode id (ForcingAtomicRelations.forces false R (fun j => up2 (base j))
          (up2 (rho 6)) 0 (up2 graph) 1))
          (memValue R (fun j => up2 (base j)) (up2 (rho 6)) (up2 X) (up2 t) (up2 f) 0 1)))
        (.forallE (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up2 (rho j)) (up2 G) (up2 (rho 6)) (up2 F) 0))
          (.forallE (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up3 (rho j)) (up3 G) (up3 (rho 6)) (up3 F) 0))
            (.iff (ProjectSyntax.encode id (ForcingFormula.formula R Hdom (fun j => up3 (base j))
              (args3 (up3 graph) 1 0) (up3 (rho 6)) 2 (Source.SetLanguage.edge 0 1 2)))
              (appValue R (fun j => up3 (base j)) (up3 (rho 6)) (up3 X) (up3 t) (up3 f) 1 0 2)))))))
  .conj (graphFormula (rho 6) X t f graph)
    (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F graph))
      (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho support graph))
        (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName t X checkedX))
          (.forallE (.imp (.mem (.bound 0) (.bound (rho 6).succ)) body)))))

theorem resultFormula_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F support X t f graph checkedX : Fin m) :
    (resultFormula R Hdom base rho G F support X t f graph checkedX).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    graphFormula_freeClosed,memValue_freeClosed,appValue_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F support X t f graph checkedX : Fin m) :
    Project.Formula.satisfies env (resultFormula R Hdom base rho G F support X t f graph checkedX) ↔
      Result R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound G) (env.bound F)
        (env.bound support) (env.bound X) (env.bound t) (env.bound f) (env.bound graph) (env.bound checkedX) := by
  simp only [resultFormula,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,graphFormula_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingFormula.formula_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),memValue_semantics hM,appValue_semantics hM]
  simp only [id_eq,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero,args2_map,args3_map]
  rfl

/-- Construct the actual source graph and all its laws together, with no
choice premise: the supplied internal function has unique pair-name values. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F support mul t X f : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env support))
    (hHF : (Project.FirstOrderSemantics.reduct M).mem (env support) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hf : FunctionOn (env X) (env f))
    (hFamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X) (env f))
    (hFixed : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i (env X) →
      PureKuratowski.PairMember M i nu (env f) → Supported (fun j => env (rho j)) (env support) nu) :
    ∃ graph checkedX, Result (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env support) (env X) (env t) (env f) graph checkedX := by
  obtain ⟨pairs,graph,hPairs,hCollected,hGraph⟩ := exists_graph hM env (rho 6) t f (env X) hf
  obtain ⟨checkedX,hChecked⟩ := ForcingCheckName.exists_checked hM (env t) (env X)
  obtain ⟨hHS,hFix⟩ := hs_and_fixed hM (fun j => env (rho j)) hPres hG hF hH hHF ht hFamily hFixed hPairs hCollected
  have htW := (hPres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r (env t) :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r (env t)).mpr (Or.inl ht)
  refine ⟨graph,checkedX,hGraph,hHS,hFix,hChecked,?_⟩
  intro p hp
  refine ⟨functionOn hM env rho G F mul t (args2 graph checkedX) 0 1 hPres hG hF ht hpre hf hChecked hFamily hGraph hp,
    fun nu => mem_graph hM htW htop hGraph hp,?_⟩
  intro x hx y hy
  exact app_graph hM env rho G F mul t (args3 graph x y) 0 1 2 hPres hG hF ht hpre hGraph hx hy hp

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F support mul t X f : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G support),
      .mem (.bound support) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty t),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (Source.SetLanguage.functionOn f X),
      ProjectSyntax.encode id (ForcingCollectedHS.familyHS rho G (rho 6) F X f),
      fixedFamily rho support X f].foldr Definitional.Formula.imp
        (.existsE (.existsE (resultFormula (orderFormula (rho 0) mul) (domain rho G F)
          (fun j => j.succ.succ) (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ support.succ.succ
          X.succ.succ t.succ.succ f.succ.succ 1 0))))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      fixedFamily_freeClosed,resultFormula_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F support mul t X f : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F support mul t X f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingCollectedHS.familyHS_semantics (M := M),
    fixedFamily_semantics hM,resultFormula_semantics hM,id_eq,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero]
  exact construct hM env rho I K B w G F support mul t X f

/-- Ordinary native ZF, in the existing pure membership language and original
proof kernel. The output includes full functionOn, raw entries, common support,
and the membership/application laws at every internal condition. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F support mul t X f : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F support mul t X f)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F support mul t X f hM)

end PPAC.Migration.ForcingIndexedGraph
