/- Pinned UniformNames.UniformInverse.LeastValue / relation:117-209.
Consumer: uniformSubsetInverse_injection -> outside_uniformRange ->
ClassFibers.outside_localList -> outsideClassSet_denseBelow.
Indices are internal ordinals of the SAME enumerated local-name carrier.
No external well-foundedness or choice of a representative is used. -/
import PPAC.Migration.ForcingCheckOrdinal
import PPAC.Migration.ForcingLocalList

namespace PPAC.Migration.ForcingUniformInverse
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingMapConditions (MapRel)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Ordinal ordinal_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def LeastValue {k : Nat} (R : Formula (k+2)) (lp : Fin k → M.Carrier .set)
    (P X f p x i : M.Carrier .set) : Prop :=
  Ordinal i ∧ (Project.FirstOrderSemantics.reduct M).mem i X ∧
    (∃ fi, PureKuratowski.PairMember M i fi f ∧ Forces true R lp P x fi p) ∧
    ∀ j fj, (Project.FirstOrderSemantics.reduct M).mem j X →
      (Project.FirstOrderSemantics.reduct M).mem j i → PureKuratowski.PairMember M j fj f →
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R lp q p →
        ¬Forces true R lp P x fj q

def leastValue {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f p x i : Fin n) : Formula n :=
  let up2 : Fin n → Fin (n+2) := fun a => a.castSucc.castSucc
  let up3 : Fin n → Fin (n+3) := fun a => a.castSucc.castSucc.castSucc
  (OrdinalSyntax.ordinal i).conj ((Formula.mem i X).conj
    ((Formula.ex ((Source.SetLanguage.edge f.castSucc i.castSucc (Fin.last n)).conj
      (forces true R (paramsUp lp) P.castSucc x.castSucc (Fin.last n) p.castSucc))).conj
    (.all (.all ((Formula.mem (Fin.last n).castSucc (up2 X)).imp
      ((Formula.mem (Fin.last n).castSucc (up2 i)).imp
        ((Source.SetLanguage.edge (up2 f) (Fin.last n).castSucc (Fin.last (n+1))).imp
          (.all ((Formula.mem (Fin.last (n+2)) (up3 P)).imp
            ((rel R (fun a => up3 (lp a)) (Fin.last (n+2)) (up3 p)).imp
              (forces true R (fun a => up3 (lp a)) (up3 P) (up3 x)
                (Fin.last (n+1)).castSucc (Fin.last (n+2))).neg))))))))))

theorem leastValue_semantics {k n : Nat} (env : Fin n → M.Carrier .set)
    (R : Formula (k+2)) (lp : Fin k → Fin n) (P X f p x i : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (leastValue R lp P X f p x i) ↔
      LeastValue R (fun a => env (lp a)) (env P) (env X) (env f) (env p) (env x) (env i) := by
  simp only [leastValue,LeastValue,Formula.Realize,Source.Formula.neg,Formula.Realize,
    ordinal_semantics (M := M),KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem least_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f p q x i : M.Carrier .set}
    (hpre : PreorderOn R lp P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R lp q p) (hi : LeastValue R lp P X f p x i) :
    LeastValue R lp P X f q x i := by
  obtain ⟨fi,hfi,hEq⟩ := hi.2.2.1
  have hp := ForcingAtomicBasic.condition hM hEq
  refine ⟨hi.1,hi.2.1,⟨fi,hfi,ForcingAtomicBasic.eq_mono hM hpre hq hqp hEq⟩,?_⟩
  intro j fj hj hji hfj r hr hrq
  exact hi.2.2.2 j fj hj hji hfj r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem least_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f p x y i : M.Carrier .set}
    (hpre : PreorderOn R lp P) (he : Forces true R lp P x y p) :
    LeastValue R lp P X f p x i ↔ LeastValue R lp P X f p y i := by
  have step {a b : M.Carrier .set} (hab : Forces true R lp P a b p)
      (hi : LeastValue R lp P X f p a i) : LeastValue R lp P X f p b i := by
    obtain ⟨fi,hfi,hai⟩ := hi.2.2.1
    refine ⟨hi.1,hi.2.1,⟨fi,hfi,ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM hab) hai⟩,?_⟩
    intro j fj hj hji hfj q hq hqp hb
    exact hi.2.2.2 j fj hj hji hfj q hq hqp
      (ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp hab) hb)
  exact ⟨step he,step (ForcingAtomicBasic.eq_symm hM he)⟩

theorem least_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f p x i j : M.Carrier .set}
    (hpre : PreorderOn R lp P) (hi : LeastValue R lp P X f p x i)
    (hj : LeastValue R lp P X f p x j) : i = j := by
  obtain hij | hij | hji := ForcingOrdinalDecision.ordinal_compare hM hi.1 hj.1
  · exact hij
  · obtain ⟨fi,hfi,hei⟩ := hi.2.2.1
    have hp := ForcingAtomicBasic.condition hM hei
    exact (hj.2.2.2 i fi hi.2.1 hij hfi p hp (hpre.1 p hp) hei).elim
  · obtain ⟨fj,hfj,hej⟩ := hj.2.2.1
    have hp := ForcingAtomicBasic.condition hM hej
    exact (hi.2.2.2 j fj hj.2.1 hji hfj p hp (hpre.1 p hp) hej).elim

def Holds {k : Nat} (R : Formula (k+2)) (lp : Fin k → M.Carrier .set)
    (P X f top p x y : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R lp q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R lp r q ∧
      ∃ i ni, Checked top i ni ∧ Forces true R lp P y ni r ∧ LeastValue R lp P X f r x i

def holds {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f top p x y : Fin n) : Formula n :=
  let up2 : Fin n → Fin (n+2) := fun a => a.castSucc.castSucc
  let up4 : Fin n → Fin (n+4) := fun a => a.castSucc.castSucc.castSucc.castSucc
  .all ((Formula.mem (Fin.last n) P.castSucc).imp
    ((rel R (paramsUp lp) (Fin.last n) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (n+1)) (up2 P)).conj
        ((rel R (fun a => up2 (lp a)) (Fin.last (n+1)) (Fin.last n).castSucc).conj
          (.ex (.ex ((checkName (up4 top) (Fin.last (n+2)).castSucc (Fin.last (n+3))).conj
            ((forces true R (fun a => up4 (lp a)) (up4 P) (up4 y)
              (Fin.last (n+3)) (Fin.last (n+1)).castSucc.castSucc).conj
              (leastValue R (fun a => up4 (lp a)) (up4 P) (up4 X) (up4 f)
                (Fin.last (n+1)).castSucc.castSucc (up4 x) (Fin.last (n+2)).castSucc))))))))))

theorem holds_semantics {k n : Nat} (env : Fin n → M.Carrier .set)
    (R : Formula (k+2)) (lp : Fin k → Fin n) (P X f top p x y : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (holds R lp P X f top p x y) ↔
      Holds R (fun a => env (lp a)) (env P) (env X) (env f) (env top) (env p) (env x) (env y) := by
  simp only [holds,Holds,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    leastValue_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem relation_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f top p x x' y y' : M.Carrier .set}
    (hpre : PreorderOn R lp P) (hx : Forces true R lp P x x' p) (hy : Forces true R lp P y y' p) :
    Holds R lp P X f top p x y ↔ Holds R lp P X f top p x' y' := by
  have hp := ForcingAtomicBasic.condition hM hx
  have step {a a' b b' : M.Carrier .set} (ha : Forces true R lp P a a' p)
      (hb : Forces true R lp P b b' p) (h : Holds R lp P X f top p a b) :
      Holds R lp P X f top p a' b' := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,ni,hni,hbi,hi⟩ := h q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    exact ⟨r,hr,hrq,i,ni,hni,
      ForcingAtomicLaws.eq_trans hM hpre
        (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hr hrp hb)) hbi,
      (least_congr hM hpre (ForcingAtomicBasic.eq_mono hM hpre hr hrp ha)).mp hi⟩
  exact ⟨step hx hy,step (ForcingAtomicBasic.eq_symm hM hx) (ForcingAtomicBasic.eq_symm hM hy)⟩

theorem relation_mono {k : Nat} {R : Formula (k+2)} {lp : Fin k → M.Carrier .set}
    {P X f top p q x y : M.Carrier .set} (hpre : PreorderOn R lp P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R lp q p)
    (h : Holds R lp P X f top p x y) : Holds R lp P X f top q x y := by
  intro r hr hrq
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem relation_regular {k : Nat} {R : Formula (k+2)} {lp : Fin k → M.Carrier .set}
    {P X f top p x y : M.Carrier .set} (hpre : PreorderOn R lp P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R lp q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R lp r q ∧ Holds R lp P X f top r x y) :
    Holds R lp P X f top p x y := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hh⟩ := h q hq hqp
  obtain ⟨s,hs,hsr,rest⟩ := hh r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,rest⟩

theorem relation_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f top p x y z : M.Carrier .set}
    (hpre : PreorderOn R lp P) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hy : Holds R lp P X f top p x y) (hz : Holds R lp P X f top p x z) :
    Forces true R lp P y z p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,i,ni,hni,hyi,hi⟩ := hy q hq hqp
  obtain ⟨s,hs,hsr,j,nj,hnj,hzj,hj⟩ := hz r hr (hpre.2 r q p hr hq hp hrq hqp)
  have hij := least_unique hM hpre (least_mono hM hpre hs hsr hi) hj
  subst j
  have hn := ForcingCheckName.unique hM hni hnj
  subst nj
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hs hsr hyi)
      (ForcingAtomicBasic.eq_symm hM hzj)⟩

theorem relation_inj (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P X f top p x y z : M.Carrier .set}
    (hpre : PreorderOn R lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R lp q top)
    (hf : ForcingConditionGraphs.FunctionOn X f)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hx : Holds R lp P X f top p x z) (hy : Holds R lp P X f top p y z) :
    Forces true R lp P x y p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,i,ni,hni,hzi,hi⟩ := hx q hq hqp
  obtain ⟨s,hs,hsr,j,nj,hnj,hzj,hj⟩ := hy r hr (hpre.2 r q p hr hq hp hrq hqp)
  have hij := (ForcingCheckReflection.eq_check_iff hM hpre ht htop hs hni hnj).mp
    (ForcingAtomicLaws.eq_trans hM hpre
      (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hs hsr hzi)) hzj)
  subst j
  obtain ⟨fi,hfi,hxi⟩ := hi.2.2.1
  obtain ⟨fj,hfj,hyj⟩ := hj.2.2.1
  have he := ForcingConditionGraphs.function_unique hf hfi hfj
  subst fj
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hs hsr hxi)
      (ForcingAtomicBasic.eq_symm hM hyj)⟩

def possible {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f q x i : Fin n) : Formula n :=
  let up2 : Fin n → Fin (n+2) := fun a => a.castSucc.castSucc
  (Formula.mem i X).conj (.ex (.ex
    ((Formula.mem (Fin.last n).castSucc (up2 P)).conj
      ((rel R (fun a => up2 (lp a)) (Fin.last n).castSucc (up2 q)).conj
        ((Source.SetLanguage.edge (up2 f) (up2 i) (Fin.last (n+1))).conj
          (forces true R (fun a => up2 (lp a)) (up2 P) (up2 x)
            (Fin.last (n+1)) (Fin.last n).castSucc))))))

theorem possible_semantics {k n : Nat} (env : Fin n → M.Carrier .set)
    (R : Formula (k+2)) (lp : Fin k → Fin n) (P X f q x i : Fin n) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (possible R lp P X f q x i) ↔
      (Project.FirstOrderSemantics.reduct M).mem (env i) (env X) ∧
      ∃ r fi, (Project.FirstOrderSemantics.reduct M).mem r (env P) ∧
        MapRel R (fun a => env (lp a)) r (env q) ∧ PureKuratowski.PairMember M (env i) fi (env f) ∧
          Forces true R (fun a => env (lp a)) (env P) (env x) fi r := by
  simp only [possible,Formula.Realize,KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Source relation_total's least-index step, using the existing object
ordinal minimum schema. Every stronger internal condition is included. -/
theorem dense_least (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (lp : Fin k → M.Carrier .set) (P X f q x : M.Carrier .set)
    (hpre : PreorderOn R lp P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hX : Ordinal X)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i X ∧
      ∃ r fi, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R lp r q ∧
        PureKuratowski.PairMember M i fi f ∧ Forces true R lp P x fi r) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R lp r q ∧
      ∃ i, LeastValue R lp P X f r x i := by
  let inputs : Fin (k+5) → M.Carrier .set :=
    Fin.lastCases x (Fin.lastCases q (Fin.lastCases f (Fin.lastCases X (Fin.lastCases P lp))))
  let matrix := possible R (fun a => a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (k+1)).castSucc.castSucc.castSucc.castSucc
    (Fin.last (k+2)).castSucc.castSucc.castSucc
    (Fin.last (k+3)).castSucc.castSucc (Fin.last (k+4)).castSucc (Fin.last (k+5))
  have hm : ∀ i, ForcingClassEvaluation.Predicate matrix inputs i ↔
      (Project.FirstOrderSemantics.reduct M).mem i X ∧
      ∃ r fi, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R lp r q ∧
        PureKuratowski.PairMember M i fi f ∧ Forces true R lp P x fi r := by
    intro i
    unfold ForcingClassEvaluation.Predicate
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      possible_semantics (M := M) (Fin.lastCases i inputs) R
        (fun a => a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc.castSucc.castSucc
        (Fin.last (k+1)).castSucc.castSucc.castSucc.castSucc
        (Fin.last (k+2)).castSucc.castSucc.castSucc
        (Fin.last (k+3)).castSucc.castSucc (Fin.last (k+4)).castSucc (Fin.last (k+5))
  have h := ForcingRawRank.closed_truth hM
    ((OrdinalLeastSyntax.has matrix id).imp (OrdinalLeastSyntax.leastExists matrix id))
    (ObjectOrdinalLeast.native_existence matrix) inputs
  simp only [OrdinalLeastSyntax.has,OrdinalLeastSyntax.leastExists,OrdinalLeastSyntax.least,
    OrdinalLeastSyntax.property,Formula.Realize,ordinal_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] at h
  obtain ⟨i,hi,r,fi,hr,hrq,hfi,hei⟩ := hne
  obtain ⟨i,⟨hoi,hpi⟩,hmin⟩ := h ⟨i,ForcingRawRank.ordinal_member hM hX hi,
    (hm i).mpr ⟨hi,r,fi,hr,hrq,hfi,hei⟩⟩
  obtain ⟨hi,r,fi,hr,hrq,hfi,hei⟩ := (hm i).mp hpi
  refine ⟨r,hr,hrq,i,hoi,hi,⟨fi,hfi,hei⟩,?_⟩
  intro j fj hj hji hfj s hs hsr he
  rcases hmin j ⟨ForcingRawRank.ordinal_member hM hX hj,
    (hm j).mpr ⟨hj,s,fj,hs,hpre.2 s r q hs hr hq hsr hrq,hfj,he⟩⟩ with hij | hij
  · exact ForcingOrdinalDecision.ordinal_irrefl hM hoi (hij.symm ▸ hji)
  · exact ForcingOrdinalDecision.ordinal_irrefl hM hoi
      (ForcingRawRank.ordinal_transitive hoi j hji i hij)

/-- Pinned UniformInverse.relation_total: the actual SAME collected local
list supplies candidates; the internal ordinal minimum supplies least ones. -/
theorem relation_total (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (lp : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {G F bound H names alpha enum list top nalpha p x : M.Carrier .set}
    (hpre : PreorderOn R lp (v 6))
    (ht : (Project.FirstOrderSemantics.reduct M).mem top (v 6))
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v 6) → MapRel R lp q top)
    (hNames : ForcingLocalNames.Carrier v G F bound H names)
    (hAlpha : Ordinal alpha)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo
      (KuratowskiZF.interpretation hM) enum alpha names)
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 alpha enum (v 6) list)
    (hChecked : Checked top alpha nalpha)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (v 6))
    (hmem : Forces false R lp (v 6) x list p) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v 6) → MapRel R lp q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (v 6) ∧ MapRel R lp r q ∧
        ∃ y, Forces false R lp (v 6) y nalpha r ∧ Holds R lp (v 6) alpha enum top r x y := by
  intro q hq hqp
  obtain ⟨s,hs,hsq,name,hn,he⟩ :=
    (ForcingLocalList.mem_localList hM R lp v hpre hNames hEnum hList hp).mp hmem q hq hqp
  obtain ⟨i,hi,hin⟩ := hEnum.2 name ((hNames name).mpr hn)
  obtain ⟨r,hr,hrq,j,hj⟩ := dense_least hM R lp (v 6) alpha enum q x hpre hq hAlpha
    ⟨i,hi,s,name,hs,hsq,hin,he⟩
  obtain ⟨nj,hnj⟩ := ForcingCheckName.exists_checked hM top j
  refine ⟨r,hr,hrq,nj,
    (ForcingCheckReflection.mem_check_check hM hpre ht htop hr hnj hChecked).mpr hj.2.1,?_⟩
  intro s hs hsr
  exact ⟨s,hs,hpre.1 s hs,j,nj,hnj,ForcingAtomicBasic.eq_refl hM hpre nj s hs,
    least_mono hM hpre hs hsr hj⟩

def denseLeastResult {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f q x : Fin n) : Formula n :=
  let up2 : Fin n → Fin (n+2) := fun a => a.castSucc.castSucc
  .ex ((Formula.mem (Fin.last n) P.castSucc).conj
    ((rel R (paramsUp lp) (Fin.last n) q.castSucc).conj
      (.ex (leastValue R (fun a => up2 (lp a)) (up2 P) (up2 X) (up2 f)
        (Fin.last n).castSucc (up2 x) (Fin.last (n+1))))))

def sentence {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f q x : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R lp P).imp ((Formula.mem q P).imp
    ((OrdinalSyntax.ordinal X).imp
      ((Formula.ex (possible R (paramsUp lp) P.castSucc X.castSucc f.castSucc
        q.castSucc x.castSucc (Fin.last n))).imp (denseLeastResult R lp P X f q x))))).close

theorem models {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f q x : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence R lp P X f q x)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env _
  simp only [Formula.Realize,ForcingAtomicBasic.preorder_semantics (M := M),
    ordinal_semantics (M := M),possible_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  intro hpre hq hX hne
  obtain ⟨r,hr,hrq,i,hi⟩ := dense_least hM R (fun a => env (lp a)) (env P) (env X)
    (env f) (env q) (env x) hpre hq hX hne
  simp only [denseLeastResult,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    leastValue_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨r,hr,hrq,i,hi⟩

theorem kernel_certificate {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f q x : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R lp P X f q x)) :=
  ModelTransfer.derives (fun _ hM => models R lp P X f q x hM)

def lawsSentence {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f top p x y z : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R lp P).imp ((Formula.mem top P).imp
    ((Formula.all ((Formula.mem (Fin.last n) P.castSucc).imp
      (rel R (paramsUp lp) (Fin.last n) top.castSucc))).imp
    ((Source.SetLanguage.functionOn f X).imp ((Formula.mem p P).imp
      (((holds R lp P X f top p x y).imp ((holds R lp P X f top p x z).imp
        (forces true R lp P y z p))).conj
      ((holds R lp P X f top p x z).imp ((holds R lp P X f top p y z).imp
        (forces true R lp P x y p))))))))).close

theorem laws_models {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f top p x y z : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (lawsSentence R lp P X f top p x y z)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env _
  simp only [Formula.Realize,ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    holds_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  intro hpre ht htop hf hp
  exact ⟨fun hy hz => relation_one hM hpre hp hy hz,
    fun hx hy => relation_inj hM hpre ht htop hf hp hx hy⟩

theorem laws_kernel_certificate {k n : Nat} (R : Formula (k+2)) (lp : Fin k → Fin n)
    (P X f top p x y z : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (lawsSentence R lp P X f top p x y z)) :=
  ModelTransfer.derives (fun _ hM => laws_models R lp P X f top p x y z hM)

end PPAC.Migration.ForcingUniformInverse
