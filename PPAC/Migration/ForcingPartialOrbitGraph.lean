/- Pinned OrbitNames.orbitGraph:254-317, used by presentationPartial.
Reuse the existing internal action/activation families and literal collector.
Each moved pair is activated at the actual moved source condition. -/
import PPAC.Migration.ForcingCompletionGraph
import PPAC.Migration.ForcingSupportOrbit
import PPAC.Migration.ForcingLabelSeparation

namespace PPAC.Migration.ForcingPartialOrbitGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingStabilizer (Action)
open ForcingSupportOrbit (NameFamily ActivationFamily)
open ForcingCollectedName (Collected Admissible)
open ForcingAtomicRelations (Forces)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingOrderedPairName (OrderedPairName)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingFormula (Force)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Entry (v : Fin 7 → M.Carrier .set) (G seed z child p : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem p (v 6) ∧ ∃ g,
    (Project.FirstOrderSemantics.reduct M).mem g G ∧ ∃ act, MapRel actionFormula v g act ∧
      Action (v 6) act seed child ∧ PureKuratowski.PairMember M z p act

/-- Full raw membership, so extra non-pair members are excluded as in source collect. -/
def Graph (v : Fin 7 → M.Carrier .set) (G seed z graph : M.Carrier .set) : Prop :=
  ∀ e, (Project.FirstOrderSemantics.reduct M).mem e graph ↔
    ∃ child p, Entry v G seed z child p ∧ PureKuratowski.Code M e child p

private def activation : Formula 3 := Source.SetLanguage.edge 0 1 2
private theorem activation_semantics (a i p : M.Carrier .set) :
    MapRel activation (fun _ : Fin 1 => a) i p ↔ PureKuratowski.PairMember M i p a := by
  simp only [MapRel,activation,KuratowskiZF.source_edge]
  rfl

private theorem admissible_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G seed z f a child p : M.Carrier .set}
    (hf : NameFamily v G seed f) (ha : ActivationFamily v G z a) :
    Admissible activation (fun _ : Fin 1 => a) G f (v 6) child p ↔ Entry v G seed z child p := by
  constructor
  · rintro ⟨hp,g,hg,hgf,hga⟩
    obtain ⟨_,act,hAct,hName⟩ := (hf g child).mp hgf
    obtain ⟨_,act',hAct',hCond⟩ := (ha g p).mp ((activation_semantics a g p).mp hga)
    have e := ForcingProductFamily.unique hM ((mapRel_action v g act').mp hAct') ((mapRel_action v g act).mp hAct)
    subst act'
    exact ⟨hp,g,hg,act,hAct,hName,hCond⟩
  · rintro ⟨hp,g,hg,act,hAct,hName,hCond⟩
    exact ⟨hp,g,hg,(hf g child).mpr ⟨hg,act,hAct,hName⟩,
      (activation_semantics a g p).mpr ((ha g p).mpr ⟨hg,act,hAct,hCond⟩)⟩

private theorem collected_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G seed z f a graph : M.Carrier .set}
    (hf : NameFamily v G seed f) (ha : ActivationFamily v G z a) :
    Collected activation (fun _ : Fin 1 => a) G f (v 6) graph ↔ Graph v G seed z graph := by
  simp only [Collected,ForcingCollectedName.Entry,Graph,admissible_iff hM hf ha]

theorem edge_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G seed z graph child p : M.Carrier .set}
    (h : Graph v G seed z graph) : PureKuratowski.PairMember M child p graph ↔ Entry v G seed z child p := by
  constructor
  · rintro ⟨e,he,hm⟩
    obtain ⟨other,q,had,hCode⟩ := (h e).mp hm
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective he hCode
    exact had
  · intro had
    obtain ⟨e,he⟩ := KuratowskiZF.exists_code hM child p
    exact ⟨e,he,(h e).mpr ⟨child,p,had,he⟩⟩

/-- This is the source collect, using the already constructed two exact
internal families. All group elements participate and the whole group fixes it. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F seed z : M.Carrier .set}
    (hPres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hSeed : HS actionFormula v G (v 6) F seed) (hz : (Project.FirstOrderSemantics.reduct M).mem z (v 6)) :
    ∃ graph, Graph v G seed z graph ∧ HS actionFormula v G (v 6) F graph ∧ Supported v G graph := by
  have hSub := ForcingSupportFilter.top_subgroup hM hG
  obtain ⟨f,a,hf,ha⟩ := ForcingSupportOrbit.exists_families hM v hPres hG (fun _ h => h) hz
  obtain ⟨graph,hGraph⟩ := ForcingCollectedName.exists_collected hM activation (fun _ : Fin 1 => a) G f (v 6)
  have hFamily := ForcingSupportOrbit.family_HS hM v hPres hG hF (fun _ h => h) hSeed hf
  have hMix := ForcingSupportOrbit.permutes hM v hPres hG hSub hz hf ha
  have hIndexed : ForcingCollectedHS.IndexedPermutes activation (fun _ : Fin 1 => a) v G G f (v 6) := by
    intro g hg act hAct i child p hi hic _hP hia
    obtain ⟨j,image,q,hj,hjf,hja,hMove,hpq⟩ := hMix g hg act hAct i child p hi hic ((activation_semantics a i p).mp hia)
    exact ⟨j,image,q,hj,hjf,(activation_semantics a j q).mpr hja,hMove,hpq⟩
  have hPerm := (ForcingCollectedHS.indexed_permutes_iff hM activation (fun _ : Fin 1 => a) v G G f).mp hIndexed
  exact ⟨graph,(collected_iff hM hf ha).mp hGraph,
    ForcingCollectedHS.collect_HS hM activation (fun _ : Fin 1 => a) v hPres hG hF hSub hF.1 hFamily hPerm hGraph,
    fun g hg act hAct => ForcingCollectedHS.fixed hM activation (fun _ : Fin 1 => a) v hPres hG hSub hFamily hPerm hGraph hg hAct⟩

def MemValue {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G seed z nu p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v 6) → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (v 6) ∧ MapRel R env r q ∧
      ∃ child activationCondition, Entry v G seed z child activationCondition ∧
        MapRel R env r activationCondition ∧ Forces true R env (v 6) nu child r

/-- Exact source mem_orbitGraph: every witness retains its actual activation. -/
theorem mem_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {G seed z graph nu p : M.Carrier .set} (hGraph : Graph v G seed z graph)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (v 6)) :
    Forces false R env (v 6) nu graph p ↔ MemValue R env v G seed z nu p := by
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · rintro ⟨_,h⟩ q hq hqp
    obtain ⟨r,child,c,hr,hrq,_hc,he,hrc,hEq⟩ := h q hq hqp
    exact ⟨r,hr,hrq,child,c,(edge_graph hM hGraph).mp he,hrc,hEq⟩
  · intro h
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,child,c,he,hrc,hEq⟩ := h q hq hqp
    exact ⟨r,child,c,hr,hrq,he.1,(edge_graph hM hGraph).mpr he,hrc,hEq⟩

def AppValue {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G left sigma z x y p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v 6) → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (v 6) ∧ MapRel R env r q ∧
      ∃ g, (Project.FirstOrderSemantics.reduct M).mem g G ∧ ∃ act, MapRel actionFormula v g act ∧
        ∃ c, PureKuratowski.PairMember M z c act ∧ MapRel R env r c ∧
          ∃ l s, Action (v 6) act left l ∧ Action (v 6) act sigma s ∧
            Forces true R env (v 6) x l r ∧ Forces true R env (v 6) y s r

private theorem pair_mapped (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w top g act left sigma seed l s child : M.Carrier .set}
    (hPres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (ht : ForcingWithTopCarrier.Empty top) (hAct : MapRel actionFormula v g act)
    (hPair : OrderedPairName top left sigma seed)
    (hl : Action (v 6) act left l) (hs : Action (v 6) act sigma s) (hChild : Action (v 6) act seed child) :
    OrderedPairName top l s child := by
  have ha := (mapRel_action v g act).mp hAct
  let params := args2 (v 6) act
  exact ForcingOrderedPairName.map_orderedPairName hM
    (ForcingConditionAction.act_function params (0 : Fin 2) 1 (ForcingProductFamily.action_permutation ha).1) hPair
    ((ForcingConditionAction.relation_semantics params (0 : Fin 2) 1 top top).mpr
      (Or.inl ⟨(hPres.2.2.2.2.2 top).mpr (Or.inl ht),ForcingProductFamily.top_fixed hPres ht ha⟩))
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 left l).mpr hl)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 sigma s).mpr hs)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 seed child).mpr hChild)

/-- Exact source app_orbitGraph, with no replacement by an evaluated universe. -/
theorem app_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    {I K B w left sigma seed z graph x y p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hPair : OrderedPairName (env top) left sigma seed)
    (hGraph : Graph (fun j => env (rho j)) (env G) seed z graph)
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x y) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
      AppValue (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) left sigma z x y p := by
  let R := orderFormula (rho 0) mul
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r (env top) :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r (env top)).mpr (Or.inl ht)
  obtain ⟨pair,hxy⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env top) x y
  rw [ForcingPairFormula.app_iff_mem_opair hM env rho G F mul (args3 graph x y) 0 1 2 hPres hG hF ht hpre hx hy hxy hp]
  change Forces false R env W pair graph p ↔ AppValue R env v7 (env G) left sigma z x y p
  rw [mem_graph hM hGraph hp]
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,child,c,⟨_hc,g,hg,act,hAct,hChild,hzc⟩,hrc,hEq⟩ := h q hq hqp
    have hPerm := (ForcingProductFamily.action_permutation ((mapRel_action v7 g act).mp hAct)).1
    obtain ⟨l,hl⟩ := ForcingNameConjugacy.exists_action hM hPerm left
    obtain ⟨s,hs⟩ := ForcingNameConjugacy.exists_action hM hPerm sigma
    obtain ⟨hxl,hys⟩ := (ForcingOrderedPairForcing.eq_opair_iff hM hpre htW hTop hxy (pair_mapped hM v7 hPres ht hAct hPair hl hs hChild)).mp hEq
    exact ⟨r,hr,hrq,g,hg,act,hAct,c,hzc,hrc,l,s,hl,hs,hxl,hys⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,g,hg,act,hAct,c,hzc,hrc,l,s,hl,hs,hxl,hys⟩ := h q hq hqp
    have hPerm := (ForcingProductFamily.action_permutation ((mapRel_action v7 g act).mp hAct)).1
    obtain ⟨child,hChild⟩ := ForcingNameConjugacy.exists_action hM hPerm seed
    have hc := hPerm.2 z c hzc
    exact ⟨r,hr,hrq,child,c,⟨hc,g,hg,act,hAct,hChild,hzc⟩,hrc,
      ForcingOrderedPairForcing.eq_opair_congr hM hpre htW hTop hxy (pair_mapped hM v7 hPres ht hAct hPair hl hs hChild) hxl hys⟩


/-- Source identity copy, retaining its actual activation condition. -/
theorem app_self (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    {I K B w left sigma seed z graph : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hPair : OrderedPairName (env top) left sigma seed)
    (hGraph : Graph (fun j => env (rho j)) (env G) seed z graph)
    (hLeft : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) left)
    (hSigma : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph left sigma) (env (rho 6)) z (Source.SetLanguage.edge 0 1 2) := by
  apply (app_graph hM env rho G F mul top hPres hG hF ht hpre hPair hGraph hLeft hSigma hz).mpr
  obtain ⟨e,he,hId⟩ := (ForcingSupportFilter.top_subgroup hM hG).2.1
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hPres ((hG e).mp he)
  have hIdentity := ForcingProductFamily.identity hM hPres hId hAct
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  let params := args2 (env (rho 6)) act
  have hFixed : ∀ name, ForcingNames.IsName (env (rho 6)) name → Action (env (rho 6)) act name name := by
    intro name hn
    exact (ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 name name).mp
      (ForcingConditionAction.name_identity hM params (0 : Fin 2) 1 hIdentity name hn)
  intro q hq hqz
  exact ⟨q,hq,hpre.1 q hq,e,he,act,(mapRel_action v7 e act).mpr hAct,z,(hIdentity z z).mpr ⟨hz,rfl⟩,hqz,
    left,sigma,hFixed left (ForcingHS.isName hLeft),hFixed sigma (ForcingHS.isName hSigma),
    ForcingAtomicBasic.eq_refl hM hpre left q hq,ForcingAtomicBasic.eq_refl hM hpre sigma q hq⟩

/-- The source compatible-center argument is a direct specialization of the
existing internal sub-diagram equation and injection extensionality. -/
theorem eq_of_common_center (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one r p q center : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hr : ForcingSupportSize.Injection D I r) (hp : ForcingSupportSize.Injection D I p) (hq : ForcingSupportSize.Injection D I q)
    (hrp : ForcingDiagramOrder.Le D mul r p) (hrq : ForcingDiagramOrder.Le D mul r q)
    (hpc : PureKuratowski.PairMember M one center p) (hqc : PureKuratowski.PairMember M one center q) : p = q := by
  obtain ⟨a,ha,hpa⟩ := hrp
  obtain ⟨b,hb,hqb⟩ := hrq
  obtain ⟨_,x,_hx,hax,hxc⟩ := (hpa one center).mp hpc
  obtain ⟨_,y,_hy,hby,hyc⟩ := (hqb one center).mp hqc
  have ex := ((hm.1.2 a ha x).2).mp hax
  have ey := ((hm.1.2 b hb y).2).mp hby
  have eab := hr.2 a b center (ex ▸ hxc) (ey ▸ hyc)
  have hqb' : ForcingDiagramOrder.Sub D mul r a q := eab.symm ▸ hqb
  exact ForcingDiagramPoset.injection_ext hM hp hq (fun u v => (hpa u v).trans (hqb' u v).symm)

/-- Pinned orbitGraph_unique. Input labels are separated at a common stronger
condition; actual moved diagram centers then identify the moved arbitrary-rank
names by the ALREADY ACCEPTED name_eq_of_same_diagram theorem. -/
theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    {I K B w one values c lo hi root J H sigma left seed d0 z graph j x y out p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hK : ¬ ForcingSupportSize.Small K w)
    (hc : ForcingSupportSize.Injection K values c) (ht : ForcingWithTopCarrier.Empty (env top))
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B) (hBits : lo ≠ hi)
    (hRoot : ForcingSupportSize.Injection (env (rho 0)) I root)
    (hRange : ForcingSupportedNames.Range (env (rho 0)) root J) (hFix : ForcingLabelPermutations.Fixing (env G) J H)
    (hSupported : Supported (fun i => env (rho i)) H sigma)
    (hSigma : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma)
    (hCenter : PureKuratowski.PairMember M one j root)
    (hLabel : ForcingLabelNames.Label (env (rho 6)) K c (env top) j hi left)
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) w d0) (hz : ForcingSupportingRoot.Code z d0 root)
    (hPair : OrderedPairName (env top) left sigma seed) (hGraph : Graph (fun i => env (rho i)) (env G) seed z graph)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hx : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) x)
    (hy : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) y)
    (hOut : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) out)
    (hY : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x y) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2))
    (hZ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x out) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2)) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y out p := by
  let R := orderFormula (rho 0) mul
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun i => env (rho i)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hAY := (app_graph hM env rho G F mul top hPres hG hF ht hpre hPair hGraph hx hy hp).mp hY
  have hAZ := (app_graph hM env rho G F mul top hPres hG hF ht hpre hPair hGraph hx hOut hp).mp hZ
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,g,hg,A,hA,a,hza,hra,l,s,hLeft,hS,hXL,hYS⟩ := hAY q hq hqp
  obtain ⟨t,htP,htr,g',hg',A',hA',a',hza',hta',l',s',hLeft',hS',hXL',hZS'⟩ :=
    hAZ r hr (hpre.2 r q p hr hq hp hrq hqp)
  have hPerm := (hG g).mp hg
  have hPerm' := (hG g').mp hg'
  have hAct := (mapRel_action v7 g A).mp hA
  have hAct' := (mapRel_action v7 g' A').mp hA'
  have hj := hRoot.1.2 one j hCenter
  obtain ⟨jg,hjj,_⟩ := hPerm.1.1.2 j hj
  obtain ⟨jg',hjj',_⟩ := hPerm'.1.1.2 j hj
  have hjg := hPerm.1.2 j jg hjj
  have hjg' := hPerm'.1.2 j jg' hjj'
  obtain ⟨labelg,hLabelg⟩ := ForcingLabelNames.exists_label hM hc.1.1 W (env top) jg hi
  obtain ⟨labelg',hLabelg'⟩ := ForcingLabelNames.exists_label hM hc.1.1 W (env top) jg' hi
  have eL := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation hAct).1 hLeft
    (ForcingLabelNames.label_move hM v7 hPres ht hPerm hAct hjj hLabel hLabelg)
  have eL' := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation hAct').1 hLeft'
    (ForcingLabelNames.label_move hM v7 hPres ht hPerm' hAct' hjj' hLabel hLabelg')
  subst labelg
  subst labelg'
  have hEqLabels := ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre htP htr hXL)) hXL'
  have eCenter : jg = jg' := by
    classical
    by_cases hn : jg = jg'
    · exact hn
    · exact False.elim (ForcingLabelSeparation.label_not_equal hM env rho mul hPres hm hw hK hc ht hlo hhi hBits hRoot hjg hjg' hn hLabelg hLabelg' hEqLabels)
  subst jg'
  obtain ⟨dg,pg,hpg,_hMoved,hCompose,hCode⟩ := ForcingSupportOrbit.moved_coordinates hM v7 hPres hPerm hA hd0 hRoot hz hza
  obtain ⟨dg',pg',hpg',_hMoved',hCompose',hCode'⟩ := ForcingSupportOrbit.moved_coordinates hM v7 hPres hPerm' hA' hd0 hRoot hz hza'
  obtain ⟨dc,pc,tc,hdc,hpc,hCodeC,htct⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hRoot htP
  have htc := ForcingSupportingRoot.code_mem hPres hdc hpc hCodeC
  have hle : MapRel R env tc t := (orderFormula_semantics env (rho 0) mul tc t).mpr htct
  have ha := (ForcingProductFamily.action_permutation hAct).1.2 z a hza
  have ha' := (ForcingProductFamily.action_permutation hAct').1.2 z a' hza'
  have htcp := hpre.2 tc t a htc htP ha hle (hpre.2 t r a htP hr ha htr hra)
  have htcp' := hpre.2 tc t a' htc htP ha' hle hta'
  have hle1 := ((ForcingSupportingRoot.code_le hCodeC hCode).mp ((orderFormula_semantics env (rho 0) mul tc a).mp htcp)).2
  have hle2 := ((ForcingSupportingRoot.code_le hCodeC hCode').mp ((orderFormula_semantics env (rho 0) mul tc a').mp htcp')).2
  have hCenter1 := (hCompose one jg).mpr ⟨hm.1.1,j,hCenter,hjj⟩
  have hCenter2 := (hCompose' one jg).mpr ⟨hm.1.1,j,hCenter,hjj'⟩
  have eDiagram := eq_of_common_center hM hm hpc hpg hpg' hle1 hle2 hCenter1 hCenter2
  subst pg'
  have eNames := ForcingSupportedNames.name_eq_of_same_diagram hM v7 hPres hG hFix hRoot hRange
    (ForcingHS.isName hSigma) hSupported hPerm hPerm' hCompose hCompose' hA hA' hS hS'
  subst s'
  exact ⟨t,htP,hpre.2 t r q htP hr hq htr hrq,ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_mono hM hpre htP htr hYS) (ForcingAtomicBasic.eq_symm hM hZS')⟩


/-- All contributed inputs belong to the actual single invariant label set. -/
theorem input (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    {I K B w c hi sigma left seed z graph j labels x y p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hc : ForcingConditionGraphs.FunctionOn K c) (hj : (Project.FirstOrderSemantics.reduct M).mem j I)
    (hLabel : ForcingLabelNames.Label (env (rho 6)) K c (env top) j hi left)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c (env top) hi labels)
    (hPair : OrderedPairName (env top) left sigma seed)
    (hGraph : Graph (fun i => env (rho i)) (env G) seed z graph)
    (hx : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) x)
    (hy : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) y)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hApp : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph x y) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2)) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x labels p := by
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun i => env (rho i)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  apply (ForcingLabelDensity.mem_labelSet hM (orderFormula (rho 0) mul) env hLabels hp htW
    (fun r _ => (orderFormula_semantics env (rho 0) mul r (env top)).mpr (Or.inl ht))).mpr
  intro q hq hqp
  obtain ⟨r,hr,hrq,g,hg,act,hAct,_a,_hza,_hra,l,_s,hLeft,_hS,hXL,_hYS⟩ :=
    ((app_graph hM env rho G F mul top hPres hG hF ht hpre hPair hGraph hx hy hp).mp hApp) q hq hqp
  have hPerm := (hG g).mp hg
  obtain ⟨jg,hjj,_⟩ := hPerm.1.1.2 j hj
  obtain ⟨labelg,hLabelg⟩ := ForcingLabelNames.exists_label hM hc W (env top) jg hi
  have eL := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation ((mapRel_action v7 g act).mp hAct)).1 hLeft
    (ForcingLabelNames.label_move hM v7 hPres ht hPerm ((mapRel_action v7 g act).mp hAct) hjj hLabel hLabelg)
  subst labelg
  exact ⟨r,jg,l,hr,hrq,hPerm.1.2 j jg hjj,hLabelg,hXL⟩

def Built {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top one K c hi root sigma labels : Fin k) : Prop :=
  ∃ j z left seed graph, PureKuratowski.PairMember M (env one) j (env root) ∧
      ForcingSupportingRoot.Code z (env top) (env root) ∧
      ForcingLabelNames.Label (env (rho 6)) (env K) (env c) (env top) j (env hi) left ∧
      OrderedPairName (env top) left (env sigma) seed ∧ Graph (fun i => env (rho i)) (env G) seed z graph ∧
      HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) graph ∧ Supported (fun i => env (rho i)) (env G) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph left (env sigma)) (env (rho 6)) z (Source.SetLanguage.edge 0 1 2) ∧
      ForcingDefaultRelation.PartialUnique (R := orderFormula (rho 0) mul) (H := domain rho G F) (env := env) (P := env (rho 6)) graph ∧
      (∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) → Forces false (orderFormula (rho 0) mul) env (env (rho 6)) left (env labels) p)

/-- Construct every piece of the source partial orbit map from the actual
supporting diagram and name. In particular the activation is (top,root), not
a supplied family or an assumed graph. The output uniqueness is proved. -/
theorem construct_partial (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top one values c lo hi root J H sigma labels : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w)) (hK : ¬ ForcingSupportSize.Small (env K) (env w))
    (hc : ForcingSupportSize.Injection (env K) (env values) (env c)) (ht : ForcingWithTopCarrier.Empty (env top))
    (hlo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hhi : (Project.FirstOrderSemantics.reduct M).mem (env hi) (env B)) (hBits : env lo ≠ env hi)
    (hRoot : ForcingSupportSize.Injection (env (rho 0)) (env I) (env root))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env root) (env J))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env J) (env H))
    (hSupported : Supported (fun i => env (rho i)) (env H) (env sigma))
    (hSigma : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env sigma))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env hi) (env labels))
    (hLabelsHS : HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env labels)) :
    Built env rho G F mul top one K c hi root sigma labels := by
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun i => env (rho i)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  obtain ⟨j,hCenter,_⟩ := hRoot.1.1.2 (env one) hm.1.1
  have hj := hRoot.1.2 (env one) j hCenter
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM (env top) (env root)
  have hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env top) := ForcingCohenCodes.empty_condition hM ht
  have hzW := ForcingSupportingRoot.code_mem hPres hd0 hRoot hz
  obtain ⟨left,hLabel⟩ := ForcingLabelNames.exists_label hM hc.1.1 W (env top) j (env hi)
  have hEdge := (ForcingLabelSet.edge_labelSet hM hLabels left (env top)).mpr ⟨rfl,j,hj,hLabel⟩
  have hLeft := ForcingHS.child hLabelsHS hEdge
  obtain ⟨seed,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env top) left (env sigma)
  have hSeed := ForcingOrderedPairName.orderedPair_hs hM v7 hPres hG hF ht hLeft hSigma hPair
  obtain ⟨graph,hGraph,hGraphHS,hGraphFixed⟩ := construct hM v7 hPres hG hF hSeed hzW
  refine ⟨j,z,left,seed,graph,hCenter,hz,hLabel,hPair,hGraph,hGraphHS,hGraphFixed,
    app_self hM env rho G F mul top hPres hG hF ht hpre hPair hGraph hLeft hSigma hzW,?_,?_⟩
  · intro p hp x hx y hy out hOut hY hZ
    exact unique hM env rho G F mul top hPres hG hF hm hw hK hc ht hlo hhi hBits hRoot hRange hFix hSupported hSigma
      hCenter hLabel hd0 hz hPair hGraph hp ((domain_semantics env rho G F x).mp hx)
      ((domain_semantics env rho G F y).mp hy) ((domain_semantics env rho G F out).mp hOut) hY hZ
  · intro p hp
    exact ForcingAtomicBasic.mem_of_edge_eq hM hpre htW
      ((orderFormula_semantics env (rho 0) mul p (env top)).mpr (Or.inl ht)) hEdge (ForcingAtomicBasic.eq_refl hM hpre left p hp)


private theorem args3_map {a : Type v1} {b : Type v2} (e : a → b) (x y z : a) :
    (fun i => e (args3 x y z i)) = args3 (e x) (e y) (e z) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

def entry {k : Nat} (rho : Fin 7 → Fin k) (G seed z child p : Fin k) : Formula k :=
  (Formula.mem p (rho 6)).conj (.ex ((Formula.mem (Fin.last k) G.castSucc).conj
    (.ex ((ReplacementPredicates.rel actionFormula (fun j => (rho j).castSucc.castSucc) (Fin.last k).castSucc (Fin.last (k+1))).conj
      ((ForcingStabilizer.action (rho 6).castSucc.castSucc (Fin.last (k+1)) seed.castSucc.castSucc child.castSucc.castSucc).conj
        (Source.SetLanguage.edge (Fin.last (k+1)) z.castSucc.castSucc p.castSucc.castSucc))))))

theorem entry_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G seed z child p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (entry rho G seed z child p) ↔
      Entry (fun i => env (rho i)) (env G) (env seed) (env z) (env child) (env p) := by
  simp only [entry,Entry,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingStabilizer.action_semantics (M := M),KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def graph {k : Nat} (rho : Fin 7 → Fin k) (G seed z name : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) name.castSucc).iff (.ex (.ex
    ((entry (fun j => (rho j).castSucc.castSucc.castSucc) G.castSucc.castSucc.castSucc
      seed.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))).conj
        (PairSyntax.ordered (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2)))))))

theorem graph_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G seed z name : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (graph rho G seed z name) ↔
      Graph (fun i => env (rho i)) (env G) (env seed) (env z) (env name) := by
  simp only [graph,Graph,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),KuratowskiZF.source_code,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

/-- Actual partial orbit map, including its all-condition unique-value law. -/
def construction {k : Nat} (rho : Fin 7 → Fin k) (G F mul top one K c hi root sigma labels : Fin k) : Formula k :=
  let up : Fin k → Fin (k+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+5) := fun i => up (rho i)
  let j := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let z := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let left := (Fin.last (k+2)).castSucc.castSucc
  let seed := (Fin.last (k+3)).castSucc
  let out := Fin.last (k+4)
  .ex (.ex (.ex (.ex (.ex ((Source.SetLanguage.edge (up root) (up one) j).conj
    ((ForcingSupportingRoot.code z (up top) (up root)).conj
    ((ForcingLabelNames.label (up (rho 6)) (up K) (up c) (up top) j (up hi) left).conj
    ((ForcingOrderedPairName.orderedPairName (up top) left (up sigma) seed).conj
    ((graph rr (up G) seed z out).conj
    ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) out).conj
    ((ForcingEquivariantMix.fixedAll rr (up G) out).conj
    ((ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up (args3 out left (up sigma)) (up (rho 6)) z (Source.SetLanguage.edge 0 1 2)).conj
    ((ForcingDefaultRelation.uniqueFormula false (orderFormula (rho 0) mul) (domain rho G F) up (up (rho 6)) out out out).conj
    ((Formula.all ((Formula.mem (Fin.last (k+5)) (up (rho 6)).castSucc).imp (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) (fun i => (up i).castSucc) (up (rho 6)).castSucc left.castSucc (up labels).castSucc (Fin.last (k+5)))))))))))))))))))

theorem construction_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top one K c hi root sigma labels : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (construction rho G F mul top one K c hi root sigma labels) ↔
      Built env rho G F mul top one K c hi root sigma labels := by
  simp only [construction,Built,Formula.Realize,KuratowskiZF.source_edge,ForcingSupportingRoot.code_semantics (M := M),
    ForcingLabelNames.label_semantics (M := M),ForcingOrderedPairName.orderedPairName_semantics (M := M),
    graph_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingEquivariantMix.fixedAll_semantics (M := M),
    ForcingFormula.formula_semantics,ForcingDefaultRelation.uniqueFormula_semantics,ForcingAtomicRelations.forces_semantics (M := M),
    Bool.false_eq_true,if_false,args3_map,Supported,ForcingDefaultRelation.PartialUnique,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def guards {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi root J H sigma labels : Fin k) : Formula k :=
  (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).conj
    ((ForcingLabelPermutations.carrier I G).conj
    ((ForcingNormalFilter.normal I G F).conj
    ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one).conj
    (((ForcingSupportSize.small K w).neg).conj
    ((Source.SetLanguage.injection c K values).conj
    ((ForcingWithTopCarrier.empty top).conj
    ((Formula.mem lo B).conj
    ((Formula.mem hi B).conj
    (((Formula.equal lo hi).neg).conj
    ((Source.SetLanguage.injection root (rho 0) I).conj
    ((ForcingSupportedNames.range (rho 0) root J).conj
    ((ForcingLabelPermutations.fixing G J H).conj
    ((ForcingEquivariantMix.fixedAll rho H sigma).conj
    ((ForcingHS.hs actionFormula rho G (rho 6) F sigma).conj
    ((ForcingLabelSet.labelSet (rho 6) I K c top hi labels).conj
    ((ForcingHS.hs actionFormula rho G (rho 6) F labels)))))))))))))))))

def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi root J H sigma labels : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (guards rho I K B w G F mul top one values c lo hi root J H sigma labels))
        (ProjectSyntax.encode id (construction rho G F mul top one K c hi root sigma labels))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi root J H sigma labels : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F mul top one values c lo hi root J H sigma labels)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),guards,Formula.Realize,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingEquivariantMix.fixedAll_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),construction_semantics]
  intro hw h
  obtain ⟨hPres,hG,hF,hm,hK,hc,ht,hlo,hhi,hBits,hRoot,hRange,hFix,hSupported,hSigma,hLabels,hLabelsHS⟩ := h
  exact construct_partial hM env rho I K B w G F mul top one values c lo hi root J H sigma labels
    hPres hG hF hm hw hK hc ht hlo hhi hBits hRoot hRange hFix hSupported hSigma hLabels hLabelsHS

/-- Full object-theory partial orbit-map construction in the original ZF
kernel, including all-condition partial uniqueness, without Choice or L. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi root J H sigma labels : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F mul top one values c lo hi root J H sigma labels)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul top one values c lo hi root J H sigma labels hM)

end PPAC.Migration.ForcingPartialOrbitGraph
