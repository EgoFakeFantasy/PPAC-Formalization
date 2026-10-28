/- Pinned EquivariantMixing.equivariantMixTest_permute / equivariantMix_fixed.
Actual consumer: Models.LocalQuotients.support_descent. The Product action,
order transport, collected-name construction and HS theorem are reused.
No permutation-invariance or HS conclusion is assumed for the mixture. -/
import PPAC.Migration.ForcingMixLaws
import PPAC.Migration.ForcingCollectedHS
import PPAC.Migration.ForcingProductSymmetry

namespace PPAC.Migration.ForcingEquivariantMix
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingMixName (Mix EdgeEntry)
open ForcingStabilizer (Action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Only change the order's parameter presentation; keep the same recursion graph. -/
theorem forces_order_congr {n k : Nat} {R : Formula (n+2)} {S : Formula (k+2)}
    {v : Fin n → M.Carrier .set} {w : Fin k → M.Carrier .set}
    (h : ∀ p q, MapRel R v p q ↔ MapRel S w p q) (e : Bool) (P x y p : M.Carrier .set) :
    Forces e R v P x y p ↔ Forces e S w P x y p := by
  simp only [Forces,ForcingAtomicGraphs.Good,ForcingAtomicStep.Equation,
    ForcingAtomicStep.MemBody,ForcingAtomicStep.EqBody,ForcingAtomicStep.EqHalf,h]

set_option maxHeartbeats 800000 in
theorem product_mem_transport (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (mul : Fin n)
    {I K B w g A x y x' y' p q : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingConditionGraphs.Permutation I g)
    (hA : MapRel actionFormula (fun j => env (rho j)) g A)
    (hx : Action (env (rho 6)) A x x') (hy : Action (env (rho 6)) A y y')
    (hpP : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q A) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x y p ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x' y' q := by
  let v : Fin (n+1) → M.Carrier .set := Fin.lastCases A env
  let R := orderFormula (rho 0).castSucc mul.castSucc
  let ac := ForcingConditionAction.actFormula (rho 6).castSucc (Fin.last n)
  have ha := (mapRel_action (fun j => env (rho j)) g A).mp hA
  have hperm := ForcingProductFamily.action_permutation ha
  have ho := ForcingProductFamily.order hM (env mul) hp hg ha
  have ho' : ForcingAtomicSymmetry.OrderOn R v (v (rho 6).castSucc) (v (Fin.last n)) := by
    simp only [v,Fin.lastCases_last,Fin.lastCases_castSucc]
    intro s t S T hs ht hS hT
    rw [orderFormula_semantics,orderFormula_semantics]
    simpa only [Fin.lastCases_castSucc] using
      (ho s t S T ((ForcingConditionAction.act_inside hs).mp hS)
        ((ForcingConditionAction.act_inside ht).mp hT)).symm
  have ht : ForcingAtomicSymmetry.Transport ac R v (env (rho 6)) := by
    have h := ForcingAtomicSymmetry.action_transport R v (rho 6).castSucc (Fin.last n)
      (by simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hperm) ho'
    simpa only [v,Fin.lastCases_castSucc] using h
  have hx' : ForcingMapConditions.Mapped ac v x x' :=
    (ForcingNameConjugacy.action_iff v (rho 6).castSucc (Fin.last n) x x').mpr
      (by simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hx)
  have hy' : ForcingMapConditions.Mapped ac v y y' :=
    (ForcingNameConjugacy.action_iff v (rho 6).castSucc (Fin.last n) y y').mpr
      (by simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hy)
  have hcond : MapRel ac v p q :=
    (ForcingConditionAction.relation_semantics v (rho 6).castSucc (Fin.last n) p q).mpr
      (by
        simp only [v,Fin.lastCases_last,Fin.lastCases_castSucc,ForcingConditionAction.Act]
        exact Or.inl ⟨hpP,hpq⟩)
  have hs := (ForcingAtomicSymmetry.atomic_symmetry hM ac R v (env (rho 6)) ht x y x' y' p q
    hx' hy' hpP hcond).1
  have hr s t : MapRel (orderFormula (rho 0) mul) env s t ↔ MapRel R v s t := by
    rw [orderFormula_semantics,orderFormula_semantics]
    simp only [v,Fin.lastCases_castSucc]
  exact (forces_order_congr hr false (env (rho 6)) x y p).trans
    (hs.trans (forces_order_congr hr false (env (rho 6)) x' y' q).symm)

def Permutes (v : Fin 7 → M.Carrier .set) (H J f a : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g H → ∀ A,
    MapRel actionFormula v g A → ∀ i sigma t,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i sigma f → PureKuratowski.PairMember M i t a →
    ∃ j tau b, (Definitional.Project.FirstOrderSemantics.reduct M).mem j J ∧
      PureKuratowski.PairMember M j tau f ∧ PureKuratowski.PairMember M j b a ∧
      Action (v 6) A sigma tau ∧ PureKuratowski.PairMember M t b A

def permutes {m : Nat} (rho : Fin 7 → Fin m) (H J f a : Fin m) : Formula m :=
  let up5 : Fin m → Fin (m+5) := fun x => x.castSucc.castSucc.castSucc.castSucc.castSucc
  let up8 : Fin m → Fin (m+8) := fun x => (up5 x).castSucc.castSucc.castSucc
  let g5 := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let A5 := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let i5 := (Fin.last (m+2)).castSucc.castSucc
  let sigma5 := (Fin.last (m+3)).castSucc
  let t5 := Fin.last (m+4)
  let j := (Fin.last (m+5)).castSucc.castSucc
  let tau := (Fin.last (m+6)).castSucc
  let b := Fin.last (m+7)
  let A := A5.castSucc.castSucc.castSucc
  let sigma := sigma5.castSucc.castSucc.castSucc
  let t := t5.castSucc.castSucc.castSucc
  let out := (Formula.mem j (up8 J)).conj ((Source.SetLanguage.edge (up8 f) j tau).conj
    ((Source.SetLanguage.edge (up8 a) j b).conj ((ForcingStabilizer.action (up8 (rho 6)) A sigma tau).conj
      (Source.SetLanguage.edge A t b))))
  let body := (Formula.mem g5 (up5 H)).imp ((rel actionFormula (fun j => up5 (rho j)) g5 A5).imp
    ((Formula.mem i5 (up5 J)).imp ((Source.SetLanguage.edge (up5 f) i5 sigma5).imp
      ((Source.SetLanguage.edge (up5 a) i5 t5).imp (.ex (.ex (.ex out)))))))
  .all (.all (.all (.all (.all body))))

theorem permutes_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin m) (H J f a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (permutes rho H J f a) ↔
      Permutes (fun j => env (rho j)) (env H) (env J) (env f) (env a) := by
  simp only [permutes,Permutes,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    KuratowskiZF.source_edge,ForcingStabilizer.action_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h g hg A hA i sigma t hi hfi hai
    exact h g A i sigma t hg hA hi hfi hai
  · intro h g A i sigma t hg hA hi hfi hai
    exact h g hg A hA i sigma t hi hfi hai

theorem move_entry (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (mul : Fin n)
    {I K B w G F H J f a g A child p image q : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I G) (hH : ForcingConjugationGraph.Subgroup I G H)
    (hf : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) G (env (rho 6)) F J f)
    (hperm : Permutes (fun j => env (rho j)) H J f a)
    (hg : (Definitional.Project.FirstOrderSemantics.reduct M).mem g H)
    (hA : MapRel actionFormula (fun j => env (rho j)) g A)
    (he : EdgeEntry (orderFormula (rho 0) mul) env (env (rho 6)) J f a child p)
    (hm : Action (env (rho 6)) A child image) (hpq : PureKuratowski.PairMember M p q A) :
    EdgeEntry (orderFormula (rho 0) mul) env (env (rho 6)) J f a image q := by
  obtain ⟨hpP,i,sigma,t,c,hi,hfi,hai,hchild,hpt,hmem⟩ := he
  obtain ⟨j,tau,b,hj,hfj,haj,hmap,htb⟩ := hperm g hg A hA i sigma t hi hfi hai
  have hact := (mapRel_action (fun j => env (rho j)) g A).mp hA
  have hAfn := (ForcingProductFamily.action_permutation hact).1
  have hc := (ForcingNames.child_condition (ForcingHS.isName (hf i sigma hi hfi)) hchild).1
  obtain ⟨c',hcc,_⟩ := hAfn.1.2 c hc
  have hfn := ForcingConditionAction.act_function (Source.SetLanguage.args2 (env (rho 6)) A) (0 : Fin 2) 1 hAfn
  have hchild' := (ForcingMapConditions.edge_mapping hM hfn hmap image c').mpr
    ⟨child,c,hchild,hm,(ForcingConditionAction.relation_semantics
      (Source.SetLanguage.args2 (env (rho 6)) A) (0 : Fin 2) 1 c c').mpr (Or.inl ⟨hc,hcc⟩)⟩
  have hpi := (hG g).mp (hH.1 g hg)
  have hord := ForcingProductFamily.order hM (env mul) hp hpi hact
  refine ⟨hAfn.2 p q hpq,j,tau,b,c',hj,hfj,haj,hchild',?_,?_⟩
  · exact (orderFormula_semantics env (rho 0) mul q b).mpr
      ((hord p t q b hpq htb).mp ((orderFormula_semantics env (rho 0) mul p t).mp hpt))
  · exact (product_mem_transport hM env rho mul hp hpi hA hm hmap hpP hpq).mp hmem

theorem child_family {v : Fin 7 → M.Carrier .set} {G F J f C idC : M.Carrier .set}
    (hC : ForcingMixName.ChildCarrier J f C) (hid : ForcingConditionGraphs.IdentityGraph C idC)
    (hf : ForcingCollectedHS.FamilyHS v G (v 6) F J f) :
    ForcingCollectedHS.FamilyHS v G (v 6) F C idC := by
  intro x child _ hxc
  obtain ⟨hx,hEq⟩ := (hid x child).mp hxc
  subst x
  obtain ⟨i,sigma,c,hi,hfi,he⟩ := (hC child).mp hx
  exact ForcingHS.child (hf i sigma hi hfi) he

theorem child_permutes (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (mul : Fin n)
    {I K B w G F H J f a C idC : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I G) (hH : ForcingConjugationGraph.Subgroup I G H)
    (hf : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) G (env (rho 6)) F J f)
    (hperm : Permutes (fun j => env (rho j)) H J f a)
    (hC : ForcingMixName.ChildCarrier J f C) (hid : ForcingConditionGraphs.IdentityGraph C idC) :
    ForcingCollectedHS.Permutes (ForcingMixName.test (orderFormula (rho 0) mul))
      (ForcingMixName.inputs env (env (rho 6)) J f a) (fun j => env (rho j)) H C idC (env (rho 6)) := by
  intro g hg A hA child p image q had hm hpq
  obtain ⟨_,x,_,hxc,htest⟩ := had
  have hxc' := ((hid x child).mp hxc).2
  subst x
  have he := (ForcingMixName.test_semantics (orderFormula (rho 0) mul) env (env (rho 6)) J f a child p).mp htest
  have he' := move_entry hM env rho mul hp hG hH hf hperm hg hA he hm hpq
  obtain ⟨i,sigma,t,c,hi,hfi,_,hc,_,_⟩ := he'.2
  have himage := (hC image).mpr ⟨i,sigma,c,hi,hfi,hc⟩
  exact ⟨he'.1,image,himage,(hid image image).mpr ⟨himage,rfl⟩,
    (ForcingMixName.test_semantics (orderFormula (rho 0) mul) env (env (rho 6)) J f a image q).mpr he'⟩

set_option maxHeartbeats 800000 in
theorem fixed_and_HS (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (mul : Fin n)
    {I K B w G F H J f a name : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H)
    (hHF : (Definitional.Project.FirstOrderSemantics.reduct M).mem H F)
    (hf : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) G (env (rho 6)) F J f)
    (hperm : Permutes (fun j => env (rho j)) H J f a)
    (hn : Mix (orderFormula (rho 0) mul) env (env (rho 6)) J f a name) :
    ForcingHS.HS actionFormula (fun j => env (rho j)) G (env (rho 6)) F name ∧
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g H → ∀ A,
        MapRel actionFormula (fun j => env (rho j)) g A → Action (env (rho 6)) A name name := by
  obtain ⟨C,hC⟩ := ForcingMixName.exists_children hM J f
  obtain ⟨idC,_,hid⟩ := ForcingConditionGraphs.exists_identity hM C
  have hcol := (ForcingMixName.collected_iff hC hid).mpr hn
  have hchild := child_family hC hid hf
  have hmove := child_permutes hM env rho mul hp hG hH hf hperm hC hid
  exact ⟨ForcingCollectedHS.collect_HS hM (ForcingMixName.test (orderFormula (rho 0) mul))
      (ForcingMixName.inputs env (env (rho 6)) J f a) (fun j => env (rho j)) hp hG hF hH hHF hchild hmove hcol,
    fun g hg A hA => ForcingCollectedHS.fixed hM (ForcingMixName.test (orderFormula (rho 0) mul))
      (ForcingMixName.inputs env (env (rho 6)) J f a) (fun j => env (rho j)) hp hG hH hchild hmove hcol hg hA⟩

def fixedAll {m : Nat} (rho : Fin 7 → Fin m) (H name : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) H.castSucc).imp (.all
    ((rel actionFormula (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (ForcingStabilizer.action (rho 6).castSucc.castSucc (Fin.last (m+1))
        name.castSucc.castSucc name.castSucc.castSucc))))

theorem fixedAll_semantics {m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin m) (H name : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fixedAll rho H name) ↔
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g (env H) → ∀ A,
        MapRel actionFormula (fun j => env (rho j)) g A →
          Action (env (rho 6)) A (env name) (env name) := by
  simp only [fixedAll,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingStabilizer.action_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {n : Nat} (rho : Fin 7 → Fin n) (mul I K B w G F H J f a : Fin n) : Source.Sentence :=
  let R := orderFormula (rho 0) mul
  let out := (ForcingMixName.mix R (paramsUp id) (rho 6).castSucc J.castSucc f.castSucc a.castSucc (Fin.last n)).conj
    ((ForcingHS.hs actionFormula (paramsUp rho) G.castSucc (rho 6).castSucc F.castSucc (Fin.last n)).conj
      (fixedAll (paramsUp rho) H.castSucc (Fin.last n)))
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((ForcingConjugationGraph.subgroup I G H).imp ((Formula.mem H F).imp
        ((ForcingCollectedHS.familyHS rho G (rho 6) F J f).imp ((permutes rho H J f a).imp (.ex out)))))))).close

theorem models {n : Nat} (rho : Fin 7 → Fin n) (mul I K B w G F H J f a : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence rho mul I K B w G F H J f a)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hH hHF hf hperm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w
    (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF
  have hH' := (ForcingConjugationGraph.subgroup_semantics (M := M) env I G H).mp hH
  have hf' := (ForcingCollectedHS.familyHS_semantics (M := M) env rho G (rho 6) F J f).mp hf
  have hperm' := (permutes_semantics (M := M) env rho H J f a).mp hperm
  obtain ⟨name,hn⟩ := ForcingMixName.exists_mix hM (orderFormula (rho 0) mul) env
    (env (rho 6)) (env J) (env f) (env a)
  obtain ⟨hs,hfix⟩ := fixed_and_HS hM env rho mul hp' hG' hF' hH' hHF hf' hperm' hn
  refine ⟨name,?_,?_,?_⟩
  · apply (ForcingMixName.mix_semantics (M := M) (Fin.lastCases name env) (orderFormula (rho 0) mul)
      (paramsUp id) (rho 6).castSucc J.castSucc f.castSucc a.castSucc (Fin.last n)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hn
  · apply (ForcingHS.hs_semantics (M := M) (Fin.lastCases name env) actionFormula (paramsUp rho)
      G.castSucc (rho 6).castSucc F.castSucc (Fin.last n)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hs
  · apply (fixedAll_semantics (M := M) (Fin.lastCases name env) (paramsUp rho) H.castSucc (Fin.last n)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hfix

theorem kernel_certificate {n : Nat} (rho : Fin 7 → Fin n) (mul I K B w G F H J f a : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence rho mul I K B w G F H J f a)) :=
  ModelTransfer.derives (fun _ hM => models rho mul I K B w G F H J f a hM)

end PPAC.Migration.ForcingEquivariantMix
