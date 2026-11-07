/- Pinned OrdinalPresentation.completionRelation/completionGraph_surjection.
The ground-indexed family is an INTERNAL function graph. Reuse the existing
literal product-entry/collected relation graphs and the full default relation;
no external family, new collector, rank cutoff or choice foundation. -/
import PPAC.Migration.ForcingDefaultRelation
import PPAC.Migration.ForcingCheckReflection
import PPAC.Migration.ForcingLabelNames

namespace PPAC.Migration.ForcingCompletionGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingClassEvaluation (Predicate)
open ForcingCheckName (Checked)
open ForcingOrderedPairName (OrderedPairName)
open ForcingDefaultRelation (Default PartialUnique)
open ForcingConditionGraphs (FunctionOn)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Completed {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P O f top X x0 x y p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i O ∧ ∃ fi, PureKuratowski.PairMember M i fi f ∧
        ∃ ci, Checked top i ci ∧ ∃ a, Predicate H env a ∧ ∃ pair, OrderedPairName top a ci pair ∧
          Forces true R env P x pair r ∧ Default R H env P fi X x0 a y r

def CartesianValue {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P top A B nu p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ a b pair, Predicate H env a ∧ Predicate H env b ∧ OrderedPairName top a b pair ∧
        Forces false R env P a A r ∧ Forces false R env P b B r ∧ Forces true R env P nu pair r

def Cover {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P O f A X p : M.Carrier .set) : Prop :=
  ∀ y, Predicate H env y → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    Forces false R env P y X q → ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
      ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
        ∃ i, (Project.FirstOrderSemantics.reduct M).mem i O ∧ ∃ fi, PureKuratowski.PairMember M i fi f ∧
          ∃ a, Predicate H env a ∧ Forces false R env P a A s ∧
            Force R H env (args3 fi a y) P s (Source.SetLanguage.edge 0 1 2)

private theorem args3_map {a : Type v1} {b : Type v2} (e : a → b) (x y z : a) :
    (fun j => e (args3 x y z j)) = args3 (e x) (e y) (e z) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

private theorem cases_map {a : Type v1} {b : Type v2} {n : Nat} (e : a → b) (x : a) (v : Fin n → a) :
    (fun j => e (Fin.cases x v j)) = Fin.cases (e x) (fun j => e (v j)) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

private theorem five_map {a : Type v1} {b : Type v2} (e : a → b) (f X x0 x y : a) :
    (fun j => e (ForcingMapCalculus.five f X x0 x y j)) =
      ForcingMapCalculus.five (e f) (e X) (e x0) (e x) (e y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

def completion {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P O f top X x0 x y p : Fin m) : Formula m :=
  let up4 : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let up5 : Fin m → Fin (m+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let up6 : Fin m → Fin (m+6) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let up7 : Fin m → Fin (m+7) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr : Fin k → Fin (m+7) := fun j => up7 (base j)
  let r := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc
  let fi := (Fin.last (m+3)).castSucc.castSucc.castSucc
  let ci := (Fin.last (m+4)).castSucc.castSucc
  let a := (Fin.last (m+5)).castSucc
  let pair := Fin.last (m+6)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (.ex ((Formula.mem (Fin.last (m+2)) O.castSucc.castSucc.castSucc).conj
            (.ex ((Source.SetLanguage.edge (up4 f) (Fin.last (m+2)).castSucc (Fin.last (m+3))).conj
              (.ex ((ForcingCheckName.checkName (up5 top) (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4))).conj
                (.ex ((MinimalPredicates.pred H (fun j => up6 (base j)) (Fin.last (m+5))).conj
                  (.ex ((ForcingOrderedPairName.orderedPairName (up7 top) a ci pair).conj
                    ((ForcingAtomicRelations.forces true R rr (up7 P) (up7 x) pair r).conj
                      (ForcingFormula.formula R H rr (ForcingMapCalculus.five fi (up7 X) (up7 x0) a (up7 y))
                        (up7 P) r ForcingDefaultRelation.defaultFormula)))))))))))))))))

theorem completion_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P O f top X x0 x y p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (completion R H base P O f top X x0 x y p) ↔
      Completed R H (fun j => env (base j)) (env P) (env O) (env f) (env top) (env X) (env x0) (env x) (env y) (env p) := by
  simp only [completion,Completed,Default,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    KuratowskiZF.source_edge,ForcingCheckName.checkName_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingOrderedPairName.orderedPairName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingFormula.formula_semantics,five_map,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def relation {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P O f top X x0 : Fin m) : Formula (m+3) :=
  completion R H (fun j => (base j).castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc O.castSucc.castSucc.castSucc
    f.castSucc.castSucc.castSucc top.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc x0.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc

theorem relation_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (base : Fin k → Fin m) (P O f top X x0 : Fin m) (p x y : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds (relation R H base P O f top X x0) env p x y ↔
      Completed R H (fun j => env (base j)) (env P) (env O) (env f) (env top) (env X) (env x0) x y p := by
  simp only [relation,ForcingRelationGraphForcing.Holds,completion_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]


section Laws
variable {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
variable {P O f top X x0 : M.Carrier .set}
variable (hpre : ForcingAtomicBasic.PreorderOn R env P)
include hpre

theorem mono {p q x y : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R env q p) (h : Completed R H env P O f top X x0 x y p) :
    Completed R H env P O f top X x0 x y q := by
  intro r hr hrq
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem regular {p x y : M.Carrier .set}
    (_hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ Completed R H env P O f top X x0 x y r) :
    Completed R H env P O f top X x0 x y p := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hR⟩ := h q hq hqp
  obtain ⟨s,hs,hsr,rest⟩ := hR r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,rest⟩

theorem at_pair (hM : FirstOrder.Theory.Models M nativeZF) {p i fi ci a pair y : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i O) (hif : PureKuratowski.PairMember M i fi f)
    (hci : Checked top i ci) (ha : Predicate H env a) (hPair : OrderedPairName top a ci pair)
    (h : Default R H env P fi X x0 a y p) : Completed R H env P O f top X x0 pair y p := by
  intro q hq hqp
  exact ⟨q,hq,hpre.1 q hq,i,hi,fi,hif,ci,hci,a,ha,pair,hPair,ForcingAtomicBasic.eq_refl hM hpre pair q hq,
    ForcingDefaultRelation.mono hM hpre hp hq hqp h⟩

theorem congr (hM : FirstOrder.Theory.Models M nativeZF) {p x x' y y' : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hxx : Forces true R env P x x' p) (hyy : Forces true R env P y y' p) :
    Completed R H env P O f top X x0 x y p ↔ Completed R H env P O f top X x0 x' y' p := by
  have step {u u' v v' : M.Carrier .set} (hu : Forces true R env P u u' p) (hv : Forces true R env P v v' p)
      (h : Completed R H env P O f top X x0 u v p) : Completed R H env P O f top X x0 u' v' p := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi,fi,hif,ci,hci,a,ha,pair,hPair,he,hD⟩ := h q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    refine ⟨r,hr,hrq,i,hi,fi,hif,ci,hci,a,ha,pair,hPair,ForcingAtomicLaws.eq_trans hM hpre
      (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hr hrp hu)) he,?_⟩
    exact (ForcingDefaultRelation.congr hM hpre hr (ForcingAtomicBasic.eq_refl hM hpre a r hr)
      (ForcingAtomicBasic.eq_mono hM hpre hr hrp hv)).mp hD
  exact ⟨step hxx hyy,step (ForcingAtomicBasic.eq_symm hM hxx) (ForcingAtomicBasic.eq_symm hM hyy)⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {p x y z : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r top)
    (hf : FunctionOn O f)
    (hUnique : ∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i O → PureKuratowski.PairMember M i fi f →
      PartialUnique (R := R) (H := H) (env := env) (P := P) fi)
    (hy : Predicate H env y) (hz : Predicate H env z)
    (hY : Completed R H env P O f top X x0 x y p) (hZ : Completed R H env P O f top X x0 x z p) :
    Forces true R env P y z p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,i,hi,fi,hif,ci,hci,a,ha,pair,hPair,hEq,hD⟩ := hY q hq hqp
  obtain ⟨s,hs,hsr,j,hj,fj,hjf,cj,hcj,b,hb,pair',hPair',hEq',hD'⟩ :=
    hZ r hr (hpre.2 r q p hr hq hp hrq hqp)
  have hPairs := ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hs hsr hEq)) hEq'
  obtain ⟨hab,hij⟩ := (ForcingOrderedPairForcing.eq_opair_iff hM hpre ht htop hPair hPair').mp hPairs
  have eq := (ForcingCheckReflection.eq_check_iff hM hpre ht htop hs hci hcj).mp hij
  subst j
  have ef := ForcingConditionGraphs.function_unique hf hjf hif
  subst fj
  have hDy := (ForcingDefaultRelation.congr hM hpre hs hab (ForcingAtomicBasic.eq_refl hM hpre y s hs)).mp
    (ForcingDefaultRelation.mono hM hpre hr hs hsr hD)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,ForcingDefaultRelation.unique hM hpre hs (hUnique i fi hi hif) hb hy hz hDy hD'⟩

theorem total (hM : FirstOrder.Theory.Models M nativeZF) {A checkedO D p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r top)
    (hChecked : Checked top O checkedO) (hf : FunctionOn O f) (hX0 : Predicate H env x0)
    (hx0 : Forces false R env P x0 X p)
    (hCart : ∀ nu q, (Project.FirstOrderSemantics.reduct M).mem q P → Forces false R env P nu D q →
      CartesianValue R H env P top A checkedO nu q) :
    ∀ x, Predicate H env x → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      Forces false R env P x D q → ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
        ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
          ∃ y, Predicate H env y ∧ Forces false R env P y X s ∧ Completed R H env P O f top X x0 x y s := by
  intro x _hx q hq hqp hx r hr hrq
  obtain ⟨s,hs,hsr,a,b,pair,ha,_hb,hPair,hA,hB,hEq⟩ := hCart x q hq hx r hr hrq
  obtain ⟨t,htP,hts,i,hi,ci,hci,hbi⟩ := (ForcingInfinity.mem_check hM hChecked ht htop hs).mp hB s hs (hpre.1 s hs)
  obtain ⟨fi,hif,_⟩ := hf.2 i hi
  have hsp := hpre.2 s q p hs hq hp (hpre.2 s r q hs hr hq hsr hrq) hqp
  have htp := hpre.2 t s p htP hs hp hts hsp
  obtain ⟨u,hu,hut,y,hy,hY,hD⟩ := ForcingDefaultRelation.total hM hpre htP hX0
    (ForcingAtomicBasic.mem_mono hM hpre htP htp hx0) t htP (hpre.1 t htP)
  obtain ⟨pair',hPair'⟩ := ForcingOrderedPairName.exists_orderedPairName hM top a ci
  have hus := hpre.2 u t s hu htP hs hut hts
  have hEq' := ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hu hus hEq)
    (ForcingOrderedPairForcing.eq_opair_congr hM hpre ht htop hPair hPair'
      (ForcingAtomicBasic.eq_refl hM hpre a u hu) (ForcingAtomicBasic.eq_mono hM hpre hu hut hbi))
  have hAt := at_pair hpre hM hu hi hif hci ha hPair' hD
  exact ⟨u,hu,hpre.2 u s r hu hs hr hus hsr,y,hy,hY,
    (congr hpre hM hu hEq' (ForcingAtomicBasic.eq_refl hM hpre y u hu)).mpr hAt⟩

theorem onto (hM : FirstOrder.Theory.Models M nativeZF) {A checkedO D p : M.Carrier .set}
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r top)
    (hChecked : Checked top O checkedO)
    (hCheck : ∀ i ci, Checked top i ci → Predicate H env ci)
    (hPairHS : ∀ a b pair, Predicate H env a → Predicate H env b → OrderedPairName top a b pair → Predicate H env pair)
    (hPairMem : ∀ a b pair s, (Project.FirstOrderSemantics.reduct M).mem s P →
      Predicate H env a → Predicate H env b → OrderedPairName top a b pair →
      Forces false R env P a A s → Forces false R env P b checkedO s → Forces false R env P pair D s)
    (hCover : Cover R H env P O f A X p) :
    ∀ y, Predicate H env y → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      Forces false R env P y X q → ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
        ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
          ∃ x, Predicate H env x ∧ Forces false R env P x D s ∧ Completed R H env P O f top X x0 x y s := by
  intro y hy q hq hqp hY r hr hrq
  obtain ⟨s,hs,hsr,i,hi,fi,hif,a,ha,hA,hApp⟩ := hCover y hy q hq hqp hY r hr hrq
  obtain ⟨ci,hci⟩ := ForcingCheckName.exists_checked hM top i
  obtain ⟨pair,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM top a ci
  have hCi := hCheck i ci hci
  have hSMy := ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hY
  exact ⟨s,hs,hsr,pair,hPairHS a ci pair ha hCi hPair,
    hPairMem a ci pair s hs ha hCi hPair hA (ForcingInfinity.check_mem_of_mem hM hpre hChecked hci hi ht htop hs),
    at_pair hpre hM hs hi hif hci ha hPair (ForcingDefaultRelation.of_app hM hpre hs hApp hSMy)⟩

end Laws

def trueRelation {k : Nat} : Formula (k+3) := .equal 0 0

private theorem true_laws {k : Nat} (R A : Formula (k+2)) (env : Fin k → M.Carrier .set) (P G F : M.Carrier .set) :
    ForcingRelationGraphForcing.Monotone R A trueRelation env P G F ∧
    ForcingRelationGraphForcing.Congruent R A trueRelation env P G F ∧
    ForcingRelationGraphForcing.Regular R A trueRelation env P G F := by
  refine ⟨?_,?_,?_⟩
  · intro p q x y _ _ _ _ _ _
    rfl
  · intro p x y x' y' _ _ _ _ _ _
    constructor <;> intro _ <;> rfl
  · intro p x y _ _ _ _
    rfl

/-- The source Cartesian name is the already accepted product-entry collector
with the always-true relation. Construct it at the actual common support. -/
theorem cartesian_construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top A C : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F)) (ht : ForcingWithTopCarrier.Empty (env top))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hC : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env C))
    (hFixA : Supported (fun j => env (rho j)) (env S) (env A))
    (hFixC : Supported (fun j => env (rho j)) (env S) (env C)) :
    ∃ D, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) trueRelation env (rho 6) top A C D ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) D ∧
      Supported (fun j => env (rho j)) (env S) D := by
  apply ForcingRelationGraphSupport.construct hM trueRelation env rho I K B w G F S mul top A C
    hPres hG hF hS ht hA hC hFixA hFixC ?_ hSF
  intro pi hpi act hAct p q x y x' y' hp hpq hx hy hxx hyy h
  rfl

theorem cartesian_mem (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top A C : Fin k)
    {I K B w D nu p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hC : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env C))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) trueRelation env (rho 6) top A C D)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu D p ↔
      ForcingRelationGraphForcing.DensePairs (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
        trueRelation env (env (rho 6)) (env G) (env F) (env top) (env A) (env C) nu p := by
  have hl := true_laws (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho) env (env (rho 6)) (env G) (env F)
  exact ForcingRelationGraphForcing.mem_graph hM _ _ _ env (rho 6) G F top A C hpre
    ((hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht))
    (fun r _ => (orderFormula_semantics env (rho 0) mul r (env top)).mpr (Or.inl ht))
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hA)
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hC) hl.1 hl.2.1 hGraph hp

theorem cartesian_pair_mem (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top A C : Fin k)
    {I K B w D a b pair p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hC : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env C))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) trueRelation env (rho 6) top A C D)
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a)
    (hb : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) b)
    (hPair : OrderedPairName (env top) a b pair) (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) pair D p ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a (env A) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b (env C) p := by
  have hl := true_laws (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho) env (env (rho 6)) (env G) (env F)
  have h := ForcingRelationGraphForcing.pair_mem_graph hM (orderFormula (rho 0) mul)
    (ForcingRelationGraphApplication.actionAt rho) trueRelation env (rho 6) G F top A C hpre
    ((hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht))
    (fun r _ => (orderFormula_semantics env (rho 0) mul r (env top)).mpr (Or.inl ht))
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hA)
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hC) hl.1 hl.2.1 hl.2.2 hGraph
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr ha)
    ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr hb) hPair hp
  simpa only [trueRelation,ForcingRelationGraphForcing.Holds,Formula.Realize,true_and,and_true] using h

theorem symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    {I K B w O f X x0 pi act p q x x' y y' : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top)) (hpi : ForcingConditionGraphs.Permutation I pi)
    (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixed : ∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i O → PureKuratowski.PairMember M i fi f →
      ForcingStabilizer.Action (env (rho 6)) act fi fi)
    (hX : ForcingStabilizer.Action (env (rho 6)) act X X) (hx0 : ForcingStabilizer.Action (env (rho 6)) act x0 x0)
    (_hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) (hpq : PureKuratowski.PairMember M p q act)
    (hxx : ForcingStabilizer.Action (env (rho 6)) act x x') (hyy : ForcingStabilizer.Action (env (rho 6)) act y y')
    (h : Completed (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) O f (env top) X x0 x y p) :
    Completed (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) O f (env top) X x0 x' y' q := by
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have ha := (mapRel_action v7 pi act).mp hAct
  have hPerm := ForcingProductFamily.action_permutation ha
  have hOrder := ForcingProductFamily.order hM (env mul) hPres hpi ha
  let ext : Fin (k+1) → M.Carrier .set := Fin.cases act env
  let up : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have hDT := ForcingSeparation.domain_transport hM ext up G.succ F.succ 0 hPres hG hF hpi hAct
  intro t htP htq
  obtain ⟨t0,ht0,ht0t⟩ := hPerm.2.2 t htP
  have ht0p := (orderFormula_semantics env (rho 0) mul t0 p).mpr
    ((hOrder t0 p t q ht0t hpq).mpr ((orderFormula_semantics env (rho 0) mul t q).mp htq))
  obtain ⟨r,hr,hrt0,i,hi,fi,hif,ci,hci,a,hA,pair,hPair,hEq,hD⟩ := h t0 ht0 ht0p
  obtain ⟨r',hrr',_⟩ := hPerm.1.1.2 r hr
  have hr' := hPerm.1.2 r r' hrr'
  have hr't := (orderFormula_semantics env (rho 0) mul r' t).mpr
    ((hOrder r t0 r' t hrr' ht0t).mp ((orderFormula_semantics env (rho 0) mul r t0).mp hrt0))
  obtain ⟨a',hA',hAa⟩ := hDT.1 a ((domain_semantics ext up G.succ F.succ a).mpr ((domain_semantics env rho G F a).mp hA))
  have hAa' := (ForcingNameConjugacy.action_iff ext (up 6) 0 a a').mp hAa
  have hCI := ForcingLabelNames.checked_fixed hM v7 hPres ht ha hci
  obtain ⟨pair',hPairAct⟩ := ForcingNameConjugacy.exists_action hM hPerm.1 pair
  let params := Source.SetLanguage.args2 (env (rho 6)) act
  have hMappedPair := ForcingOrderedPairName.map_orderedPairName hM
    (ForcingConditionAction.act_function params (0 : Fin 2) 1 hPerm.1) hPair
    ((ForcingConditionAction.relation_semantics params (0 : Fin 2) 1 (env top) (env top)).mpr
      (Or.inl ⟨(hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht),ForcingProductFamily.top_fixed hPres ht ha⟩))
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 a a').mpr hAa')
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 ci ci).mpr hCI)
    ((ForcingNameConjugacy.action_iff params (0 : Fin 2) 1 pair pair').mpr hPairAct)
  have hEq' := (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct (.equal (0 : Fin 2) 1)
    (Source.SetLanguage.args2 x pair) (Source.SetLanguage.args2 x' pair')
    (fun j => Fin.cases hxx (Fin.cases hPairAct (fun i => Fin.elim0 i)) j) hr hrr').mp hEq
  exact ⟨r',hr',hr't,i,hi,fi,hif,ci,hci,a',
    (domain_semantics env rho G F a').mpr ((domain_semantics ext up G.succ F.succ a').mp hA'),
    pair',hMappedPair,hEq',(ForcingDefaultRelation.symmetry hM env rho G F mul hPres hG hF hpi hAct
      (hFixed i fi hi hif) hX hx0 hr hrr' hAa' hyy).mp hD⟩


/-- Environment extension preserves the exact forcing relation, including its
unrestricted HS quantifiers. This transports the source inputs, not an external
choice of their witnesses. -/
theorem cover_congr {k l : Nat} {R : Formula (k+2)} {S : Formula (l+2)}
    {H : Formula (k+1)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J other x)
    (P O f A X p : M.Carrier .set) : Cover R H env P O f A X p ↔ Cover S J other P O f A X p := by
  simp only [Cover,hR,hH,ForcingSeparation.atomic_congr hR,ForcingSeparation.force_congr hR hH]

theorem partialUnique_congr {k l : Nat} {R : Formula (k+2)} {S : Formula (l+2)}
    {H : Formula (k+1)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J other x)
    (P f : M.Carrier .set) :
    PartialUnique (R := R) (H := H) (env := env) (P := P) f ↔
      PartialUnique (R := S) (H := J) (env := other) (P := P) f := by
  simp only [PartialUnique,hH,ForcingSeparation.atomic_congr hR,ForcingSeparation.force_congr hR hH]

private theorem checked_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t x checked : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t) (hc : Checked t x checked) :
    HS actionFormula v G (v 6) F checked := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x checked hc
  intro pi hpi
  obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG pi).mp hpi)
  exact ⟨act,(mapRel_action v pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
    Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ha⟩⟩

/-- Source completionGraph_surjection at a constructed Cartesian domain. The
three graph laws are proved from the original partial maps and dense cover;
no completed graph, total function, or surjectivity premise is supplied. -/
theorem construct_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top O f D X x0 : Fin k)
    {p checkedO A : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F)) (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hChecked : Checked (env top) (env O) checkedO) (hf : FunctionOn (env O) (env f))
    (hD : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env D))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hX0 : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env x0))
    (hFixD : Supported (fun j => env (rho j)) (env S) (env D))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hFixX0 : Supported (fun j => env (rho j)) (env S) (env x0))
    (hInvariant : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi (env G) → ∀ act,
      MapRel actionFormula (fun j => env (rho j)) pi act → ∀ i fi,
      (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i fi (env f) →
      ForcingStabilizer.Action (env (rho 6)) act fi fi)
    (hUnique : ∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i fi (env f) →
      PartialUnique (R := orderFormula (rho 0) mul) (H := domain rho G F) (env := env) (P := env (rho 6)) fi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hx0 : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (env x0) (env X) p)
    (hCart : ∀ nu q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env D) q →
      CartesianValue (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env top) A checkedO nu q)
    (hPairMem : ∀ a b pair s, (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6)) →
      Predicate (domain rho G F) env a → Predicate (domain rho G F) env b → OrderedPairName (env top) a b pair →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a A s →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b checkedO s →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) pair (env D) s)
    (hCover : Cover (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env O) (env f) A (env X) p) :
    ∃ graph, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun j => env (rho j)) (env S) graph ∧
      ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
        (relation (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) O f top X x0) env (rho 6) top D X graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env D) (env X)) (env (rho 6)) p
        (Source.SetLanguage.surjection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let Q := relation R H id (rho 6) O f top X x0
  have hQ : ∀ p x y, ForcingRelationGraphForcing.Holds Q env p x y ↔
      Completed R H env W (env O) (env f) (env top) (env X) (env x0) x y p :=
    fun p x y => relation_semantics env R H id (rho 6) O f top X x0 p x y
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hHA : ∀ x, HS (ForcingRelationGraphApplication.actionAt rho) env (env G) W (env F) x ↔ Predicate H env x :=
    fun x => (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ x).trans (domain_semantics env rho G F x).symm
  have hmono : ForcingRelationGraphForcing.Monotone R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro p q x y hp hq hqp _ _ h
    exact (hQ q x y).mpr (mono hpre hp hq hqp ((hQ p x y).mp h))
  have hcongr : ForcingRelationGraphForcing.Congruent R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro p x y x' y' _ _ _ _ he he'
    exact (hQ p x y).trans ((congr hpre hM ((ForcingAtomicRelations.eq_iff hM R env W x x' p).mp he).1 he he').trans (hQ p x' y').symm)
  have hregular : ForcingRelationGraphForcing.Regular R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro p x y hp _ _ hd
    apply (hQ p x y).mpr
    apply regular hpre hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,hh⟩ := hd q hq hqp
    exact ⟨r,hr,hrq,(hQ r x y).mp hh⟩
  have hMoves : ForcingRelationGraphSupport.Moves Q env rho G F S := by
    intro pi hpi act hAct q r x y x' y' hq hqr _ _ hxx hyy h
    apply (hQ r x' y').mpr
    exact symmetry hM env rho G F mul top hPres hG hF ht ((hG pi).mp (hS.1 pi hpi)) hAct
      (hInvariant pi (hS.1 pi hpi) act hAct) (hFixX pi hpi act hAct) (hFixX0 pi hpi act hAct)
      hq hqr hxx hyy ((hQ q x y).mp h)
  obtain ⟨graph,hGraph,hHS,hSupport⟩ := ForcingRelationGraphSupport.construct hM Q env rho I K B w G F S mul top D X
    hPres hG hF hS ht hD hX hFixD hFixX hMoves hSF
  refine ⟨graph,hHS,hSupport,hGraph,?_⟩
  apply ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top D X Q (args3 graph (env D) (env X))
    (0 : Fin 3) 1 2 hPres hG hF ht hpre hD hX hmono hcongr hregular hGraph rfl rfl ?_ ?_ ?_ hp
  · intro x hx q hq hqp hMem r hr hrq
    obtain ⟨s,hs,hsr,y,hy,hY,hC⟩ := total hpre hM hp htW htop hChecked hf
      ((domain_semantics env rho G F (env x0)).mpr hX0) hx0 hCart x ((hHA x).mp hx) q hq hqp hMem r hr hrq
    exact ⟨s,hs,hsr,y,(hHA y).mpr hy,hY,(hQ s x y).mpr hC⟩
  · intro q hq _ x y z _ hy hz hY hZ
    exact unique hpre hM hq htW htop hf hUnique ((hHA y).mp hy) ((hHA z).mp hz) ((hQ q x y).mp hY) ((hQ q x z).mp hZ)
  · intro y hy q hq hqp hY r hr hrq
    have hCheck : ∀ i ci, Checked (env top) i ci → Predicate H env ci := by
      intro i ci hci
      exact (domain_semantics env rho G F ci).mpr (checked_hs hM (fun j => env (rho j)) hPres hG hF ht hci)
    have hPairHS : ∀ a b pair, Predicate H env a → Predicate H env b → OrderedPairName (env top) a b pair → Predicate H env pair := by
      intro a b pair ha hb hPair
      exact (domain_semantics env rho G F pair).mpr (ForcingOrderedPairName.orderedPair_hs hM (fun j => env (rho j)) hPres hG hF ht
        ((domain_semantics env rho G F a).mp ha) ((domain_semantics env rho G F b).mp hb) hPair)
    obtain ⟨s,hs,hsr,x,hx,hD,hC⟩ := onto hpre hM htW htop hChecked hCheck hPairHS hPairMem hCover y ((hHA y).mp hy) q hq hqp hY r hr hrq
    exact ⟨s,hs,hsr,x,(hHA x).mpr hx,hD,(hQ s x y).mpr hC⟩


def Built {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul top O A X x0 : Fin k) (p : M.Carrier .set) : Prop :=
  ∃ S checkedO D graph,
      ForcingConjugationGraph.Subgroup (env I) (env G) S ∧ (Project.FirstOrderSemantics.reduct M).mem S (env F) ∧
      ForcingTupleStabilizer.TupleFixed (fun j => env (rho j)) (env G) (env (rho 6)) (args3 (env A) (env X) (env x0)) S ∧
      Checked (env top) (env O) checkedO ∧
      ForcingRelationGraph.Graph (orderFormula (rho 0).succ.succ mul.succ.succ) trueRelation
        (Fin.cases S (Fin.cases checkedO env)) (rho 6).succ.succ top.succ.succ A.succ.succ 1 D ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) D ∧ Supported (fun j => env (rho j)) S D ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧ Supported (fun j => env (rho j)) S graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph D (env X)) (env (rho 6)) p
        (Source.SetLanguage.surjection 0 1 2)

/-- Construct the support, check(O), the literal Cartesian domain and the
completed graph. The family, partial uniqueness, default member and dense
coverage are exactly the explicit source inputs. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top O f A X x0 : Fin k)
    {p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hf : FunctionOn (env O) (env f))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hX0 : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env x0))
    (hInvariant : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi (env G) → ∀ act,
      MapRel actionFormula (fun j => env (rho j)) pi act → ∀ i fi,
      (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i fi (env f) →
      ForcingStabilizer.Action (env (rho 6)) act fi fi)
    (hUnique : ∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i fi (env f) →
      PartialUnique (R := orderFormula (rho 0) mul) (H := domain rho G F) (env := env) (P := env (rho 6)) fi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hx0 : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (env x0) (env X) p)
    (hCover : Cover (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env O) (env f) (env A) (env X) p) :
    Built env rho I G F mul top O A X x0 p := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  obtain ⟨S,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM v7 hPres hG hF
    (args3 (env A) (env X) (env x0)) (fun j => Fin.cases hA (Fin.cases hX (Fin.cases hX0 (fun i => Fin.elim0 i))) j)
  obtain ⟨checkedO,hChecked⟩ := ForcingCheckName.exists_checked hM (env top) (env O)
  have hC := checked_hs hM v7 hPres hG hF ht hChecked
  let ec : Fin (k+2) → M.Carrier .set := Fin.cases S (Fin.cases checkedO env)
  let rc : Fin 7 → Fin (k+2) := fun j => (rho j).succ.succ
  let Rc := orderFormula (rc 0) mul.succ.succ
  have hRc : ∀ a b, MapRel R env a b ↔ MapRel Rc ec a b := by
    intro a b
    exact (orderFormula_semantics env (rho 0) mul a b).trans (orderFormula_semantics ec (rc 0) mul.succ.succ a b).symm
  have hprec : ForcingAtomicBasic.PreorderOn Rc ec W := by
    exact ⟨fun a ha => (hRc a a).mp (hpre.1 a ha),fun a b c ha hb hc hab hbc =>
      (hRc a c).mp (hpre.2 a b c ha hb hc ((hRc a b).mpr hab) ((hRc b c).mpr hbc))⟩
  have hFixA : Supported v7 S (env A) := fun pi hpi act hAct => ForcingTupleStabilizer.fixed_action hM hTuple hpi hAct (0 : Fin 3)
  have hFixX : Supported v7 S (env X) := fun pi hpi act hAct => ForcingTupleStabilizer.fixed_action hM hTuple hpi hAct (1 : Fin 3)
  have hFixX0 : Supported v7 S (env x0) := fun pi hpi act hAct => ForcingTupleStabilizer.fixed_action hM hTuple hpi hAct (2 : Fin 3)
  have hFixC : Supported v7 S checkedO := by
    intro pi hpi act hAct
    exact ForcingLabelNames.checked_fixed hM v7 hPres ht ((mapRel_action v7 pi act).mp hAct) hChecked
  obtain ⟨D,hCartesian,hD,hFixD⟩ := cartesian_construct hM ec rc I.succ.succ K.succ.succ B.succ.succ w.succ.succ
    G.succ.succ F.succ.succ 0 mul.succ.succ top.succ.succ A.succ.succ 1 hPres hG hF hS hSF ht hA hC hFixA hFixC
  let eg : Fin (k+3) → M.Carrier .set := Fin.cases D ec
  let rg : Fin 7 → Fin (k+3) := fun j => (rc j).succ
  let Rg := orderFormula (rg 0) mul.succ.succ.succ
  let Hg := domain rg G.succ.succ.succ F.succ.succ.succ
  have hRg : ∀ a b, MapRel R env a b ↔ MapRel Rg eg a b := by
    intro a b
    exact (orderFormula_semantics env (rho 0) mul a b).trans (orderFormula_semantics eg (rg 0) mul.succ.succ.succ a b).symm
  have hRcg : ∀ a b, MapRel Rc ec a b ↔ MapRel Rg eg a b := fun a b => (hRc a b).symm.trans (hRg a b)
  have hHg : ∀ x, Predicate H env x ↔ Predicate Hg eg x := by
    intro x
    exact (domain_semantics env rho G F x).trans (domain_semantics eg rg G.succ.succ.succ F.succ.succ.succ x).symm
  have hpreg : ForcingAtomicBasic.PreorderOn Rg eg W :=
    ⟨fun a ha => (hRg a a).mp (hpre.1 a ha),fun a b c ha hb hc hab hbc =>
      (hRg a c).mp (hpre.2 a b c ha hb hc ((hRg a b).mpr hab) ((hRg b c).mpr hbc))⟩
  have hCart : ∀ nu q, (Project.FirstOrderSemantics.reduct M).mem q W → Forces false Rg eg W nu D q →
      CartesianValue Rg Hg eg W (env top) (env A) checkedO nu q := by
    intro nu q hq hMem r hr hrq
    have hd := (cartesian_mem hM ec rc G.succ.succ F.succ.succ mul.succ.succ top.succ.succ A.succ.succ 1
      hPres ht hprec hA hC hCartesian hq).mp ((ForcingSeparation.atomic_congr hRcg false W nu D q).mpr hMem)
    obtain ⟨s,hs,hsr,a,b,pair,ha,hb,hPair,hMA,hMB,_,hEq⟩ := hd r hr ((hRcg r q).mpr hrq)
    refine ⟨s,hs,(hRcg s r).mp hsr,a,b,pair,?_,?_,hPair,
      (ForcingSeparation.atomic_congr hRcg false W a (env A) s).mp hMA,
      (ForcingSeparation.atomic_congr hRcg false W b checkedO s).mp hMB,
      (ForcingSeparation.atomic_congr hRcg true W nu pair s).mp hEq⟩
    · exact (domain_semantics eg rg G.succ.succ.succ F.succ.succ.succ a).mpr
        ((ForcingRelationGraphApplication.hs_actionAt ec rc _ _ _ a).mp ha)
    · exact (domain_semantics eg rg G.succ.succ.succ F.succ.succ.succ b).mpr
        ((ForcingRelationGraphApplication.hs_actionAt ec rc _ _ _ b).mp hb)
  have hPairMem : ∀ a b pair s, (Project.FirstOrderSemantics.reduct M).mem s W → Predicate Hg eg a → Predicate Hg eg b →
      OrderedPairName (env top) a b pair → Forces false Rg eg W a (env A) s → Forces false Rg eg W b checkedO s →
      Forces false Rg eg W pair D s := by
    intro a b pair s hs ha hb hPair hMA hMB
    apply (ForcingSeparation.atomic_congr hRcg false W pair D s).mp
    apply (cartesian_pair_mem hM ec rc G.succ.succ F.succ.succ mul.succ.succ top.succ.succ A.succ.succ 1
      hPres ht hprec hA hC hCartesian ((domain_semantics eg rg G.succ.succ.succ F.succ.succ.succ a).mp ha)
      ((domain_semantics eg rg G.succ.succ.succ F.succ.succ.succ b).mp hb) hPair hs).mpr
    exact ⟨(ForcingSeparation.atomic_congr hRcg false W a (env A) s).mpr hMA,
      (ForcingSeparation.atomic_congr hRcg false W b checkedO s).mpr hMB⟩
  obtain ⟨graph,hGraphHS,hGraphFix,_hGraph,hSurj⟩ := construct_graph hM eg rg I.succ.succ.succ K.succ.succ.succ
    B.succ.succ.succ w.succ.succ.succ G.succ.succ.succ F.succ.succ.succ 1 mul.succ.succ.succ top.succ.succ.succ
    O.succ.succ.succ f.succ.succ.succ 0 X.succ.succ.succ x0.succ.succ.succ
    hPres hG hF hS hSF ht hpreg hChecked hf hD hX hX0 hFixD hFixX hFixX0 hInvariant
    (fun i fi hi hif => (partialUnique_congr hRg hHg W fi).mp (hUnique i fi hi hif)) hp
    ((ForcingSeparation.atomic_congr hRg false W (env x0) (env X) p).mp hx0) hCart hPairMem
    ((cover_congr hRg hHg W (env O) (env f) (env A) (env X) p).mp hCover)
  exact ⟨S,checkedO,D,graph,hS,hSF,hTuple,hChecked,hCartesian,hD,hFixD,hGraphHS,hGraphFix,
    (ForcingSeparation.force_congr hRg hHg (Source.SetLanguage.surjection (0 : Fin 3) 1 2) (args3 graph D (env X)) W p).mpr hSurj⟩


/-- Exact dense covering input of the pinned source theorem. -/
def covering {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P O f A X p : Fin m) : Formula m :=
  let up4 : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let up5 : Fin m → Fin (m+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let up6 : Fin m → Fin (m+6) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let up7 : Fin m → Fin (m+7) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr : Fin k → Fin (m+7) := fun j => up7 (base j)
  let y := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let s := (Fin.last (m+3)).castSucc.castSucc.castSucc
  let a := Fin.last (m+6)
  .all ((MinimalPredicates.pred H (fun j => (base j).castSucc) (Fin.last m)).imp
    (.all ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
      ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) p.castSucc.castSucc).imp
        ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc.castSucc) P.castSucc.castSucc
          (Fin.last m).castSucc X.castSucc.castSucc (Fin.last (m+1))).imp
          (.all ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).imp
            ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+2)) (Fin.last (m+1)).castSucc).imp
              (.ex ((Formula.mem (Fin.last (m+3)) (up4 P)).conj
                ((ReplacementPredicates.rel R (fun j => up4 (base j)) (Fin.last (m+3)) (Fin.last (m+2)).castSucc).conj
                  (.ex ((Formula.mem (Fin.last (m+4)) (up5 O)).conj
                    (.ex ((Source.SetLanguage.edge (up6 f) (Fin.last (m+4)).castSucc (Fin.last (m+5))).conj
                      (.ex ((MinimalPredicates.pred H rr a).conj
                        ((ForcingAtomicRelations.forces false R rr (up7 P) a (up7 A) s).conj
                          (ForcingFormula.formula R H rr (args3 (Fin.last (m+5)).castSucc a y) (up7 P) s
                            (Source.SetLanguage.edge 0 1 2))))))))))))))))))))

theorem covering_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P O f A X p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (covering R H base P O f A X p) ↔
      Cover R H (fun j => env (base j)) (env P) (env O) (env f) (env A) (env X) (env p) := by
  simp only [covering,Cover,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingFormula.formula_semantics,KuratowskiZF.source_edge,args3_map,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def invariant {k : Nat} (rho : Fin 7 → Fin k) (G O f : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) O.castSucc).imp (.all
    ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).imp
      (ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc.castSucc) G.castSucc.castSucc (Fin.last (k+1))))))

theorem invariant_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G O f : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (invariant rho G O f) ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∀ fi, PureKuratowski.PairMember M i fi (env f) →
        Supported (fun j => env (rho j)) (env G) fi := by
  simp only [invariant,Supported,Formula.Realize,KuratowskiZF.source_edge,
    ForcingEquivariantMix.fixedAll_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def partialFamily {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P O f X x0 : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) O.castSucc).imp (.all
    ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (ForcingDefaultRelation.uniqueFormula false R H (fun j => (base j).castSucc.castSucc)
        P.castSucc.castSucc (Fin.last (m+1)) X.castSucc.castSucc x0.castSucc.castSucc))))

theorem partialFamily_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P O f X x0 : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (partialFamily R H base P O f X x0) ↔
      ∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i fi (env f) →
        PartialUnique (R := R) (H := H) (env := fun j => env (base j)) (P := env P) fi := by
  simp only [partialFamily,Formula.Realize,KuratowskiZF.source_edge,ForcingDefaultRelation.uniqueFormula_semantics,
    Bool.false_eq_true,if_false,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h i fi hi hif => h i hi fi hif,fun h i hi fi hif => h i fi hi hif⟩

/-- All four new internal sets are existentially constructed. In particular D
is constrained by the exact already accepted Cartesian collector, and the
surjection formula retains source functionOn, mapsTo and onto in full. -/
def construction {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top O A X x0 p : Fin k) : Formula k :=
  let up : Fin k → Fin (k+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+4) := fun j => up (rho j)
  let S := (Fin.last k).castSucc.castSucc.castSucc
  let cO := (Fin.last (k+1)).castSucc.castSucc
  let D := (Fin.last (k+2)).castSucc
  let graph := Fin.last (k+3)
  let rc : Fin 7 → Fin (k+2) := fun j => (rho j).succ.succ
  let bc : Fin (k+2) → Fin (k+4) := Fin.cases S (Fin.cases cO up)
  .ex (.ex (.ex (.ex
    ((ForcingConjugationGraph.subgroup (up I) (up G) S).conj
      ((Formula.mem S (up F)).conj
        ((ForcingTupleStabilizer.tupleFixed rr (up G) (up (rho 6)) (args3 (up A) (up X) (up x0)) S).conj
          ((ForcingCheckName.checkName (up top) (up O) cO).conj
            ((ForcingRelationGraph.graph (orderFormula (rc 0) mul.succ.succ) trueRelation bc (rc 6) top.succ.succ A.succ.succ 1 D).conj
              ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) D).conj
                ((ForcingEquivariantMix.fixedAll rr S D).conj
                  ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) graph).conj
                    ((ForcingEquivariantMix.fixedAll rr S graph).conj
                      (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
                        (args3 graph D (up X)) (up (rho 6)) (up p) (Source.SetLanguage.surjection 0 1 2))))))))))))))

theorem construction_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul top O A X x0 p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (construction rho I G F mul top O A X x0 p) ↔
      Built env rho I G F mul top O A X x0 (env p) := by
  simp only [construction,Built,Formula.Realize,ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingTupleStabilizer.tupleFixed_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingRelationGraph.graph_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingEquivariantMix.fixedAll_semantics (M := M),ForcingFormula.formula_semantics,
    args3_map,cases_map,Supported,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f A X x0 p : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingWithTopCarrier.empty top).imp
    ((ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp
    ((Source.SetLanguage.functionOn f O).imp
    ((ForcingCollectedHS.familyHS rho G (rho 6) F O f).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F A).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F X).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F x0).imp
    ((invariant rho G O f).imp
    ((partialFamily (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) O f X x0).imp
    ((Formula.mem p (rho 6)).imp
    ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x0 X p).imp
    ((covering (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) O f A X p).imp
      (construction rho I G F mul top O A X x0 p)))))))))))))))).close

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f A X x0 p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence rho I K B w G F mul top O f A X x0 p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hPres hG hF ht hpre hf _hFamily hA hX hX0 hInvariant hUnique hp hx0 hCover
  apply (construction_semantics env rho I G F mul top O A X x0 p).mpr
  apply construct hM env rho I K B w G F mul top O f A X x0
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hPres)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env top).mp ht)
    ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre)
    ((ForcingConditionGraphs.functionOn_semantics (M := M) env O f).mp hf)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F A).mp hA)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F x0).mp hX0)
    (fun pi hpi act hAct i fi hi hif => ((invariant_semantics env rho G O f).mp hInvariant) i hi fi hif pi hpi act hAct)
    ((partialFamily_semantics env (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) O f X x0).mp hUnique)
    hp ((ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) x0 X p).mp hx0)
    ((covering_semantics env (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) O f A X p).mp hCover)

/-- Original pure-membership derivation of the complete pinned auxiliary
surjection theorem. This is a ZF theorem scheme, with no Choice or L wrapper. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f A X x0 p : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence rho I K B w G F mul top O f A X x0 p)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul top O f A X x0 p hM)

end PPAC.Migration.ForcingCompletionGraph
