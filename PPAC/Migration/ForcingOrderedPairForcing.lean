/- Fixed OrbitNames.eq_pair_congr/mem_singleton/eq_pair_singleton/
eq_pair_cancel_left/eq_opair_congr/eq_opair_iff, consumed by
TailGraphs.BinaryRelation.mem_graph/app_graph. Reuse actual atomic laws,
literal pair names and density regularity; no pair-quotient axiom. -/
import PPAC.Migration.ForcingOrderedPairName
import PPAC.Migration.ForcingPairUnion

namespace PPAC.Migration.ForcingOrderedPairForcing
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingPairName (PairName)
open ForcingOrderedPairName (OrderedPairName)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem mem_pair_left (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y name p : M.Carrier .set} (hn : PairName t x y name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) : Forces false R env P x name p :=
  ForcingAtomicBasic.mem_of_edge_eq hM hpre ht (htop p hp)
    ((ForcingPairName.edge_pairName hM hn x t).mpr ⟨Or.inl rfl,rfl⟩)
    (ForcingAtomicBasic.eq_refl hM hpre x p hp)

theorem mem_pair_right (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y name p : M.Carrier .set} (hn : PairName t x y name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) : Forces false R env P y name p :=
  ForcingAtomicBasic.mem_of_edge_eq hM hpre ht (htop p hp)
    ((ForcingPairName.edge_pairName hM hn y t).mpr ⟨Or.inr rfl,rfl⟩)
    (ForcingAtomicBasic.eq_refl hM hpre y p hp)

theorem eq_pair_congr (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y x' y' a b p : M.Carrier .set} (ha : PairName t x y a) (hb : PairName t x' y' b)
    (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p) : Forces true R env P a b p := by
  have hp := ForcingAtomicBasic.condition hM hx
  have step {x y x' y' a b : M.Carrier .set}
      (ha : PairName t x y a) (hb : PairName t x' y' b)
      (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p) :
      ForcingAtomicRelations.EqHalf R env P a b p := by
    intro nu c _ he q hq hqp _
    rcases ((ForcingPairName.edge_pairName hM ha nu c).mp he).1 with h | h
    · subst nu
      exact ForcingAtomicBasic.mem_of_edge_eq hM hpre ht (htop q hq)
        ((ForcingPairName.edge_pairName hM hb x' t).mpr ⟨Or.inl rfl,rfl⟩)
        (ForcingAtomicBasic.eq_mono hM hpre hq hqp hx)
    · subst nu
      exact ForcingAtomicBasic.mem_of_edge_eq hM hpre ht (htop q hq)
        ((ForcingPairName.edge_pairName hM hb y' t).mpr ⟨Or.inr rfl,rfl⟩)
        (ForcingAtomicBasic.eq_mono hM hpre hq hqp hy)
  exact (ForcingAtomicRelations.eq_iff hM R env P a b p).mpr
    ⟨hp,step ha hb hx hy,step hb ha (ForcingAtomicBasic.eq_symm hM hx) (ForcingAtomicBasic.eq_symm hM hy)⟩

theorem mem_singleton (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y name p : M.Carrier .set} (hn : PairName t y y name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P x name p ↔ Forces true R env P x y p := by
  rw [ForcingPairUnion.mem_pair hM hn ht htop hp]
  constructor
  · intro h
    apply ForcingAtomicBasic.eq_of_dense hM hpre hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,he⟩ := h q hq hqp
    exact ⟨r,hr,hrq,he.elim id id⟩
  · intro h q hq hqp
    exact ⟨q,hq,hpre.1 q hq,Or.inl (ForcingAtomicBasic.eq_mono hM hpre hq hqp h)⟩

theorem eq_pair_singleton (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y z a b p : M.Carrier .set} (ha : PairName t x y a) (hb : PairName t z z b)
    (he : Forces true R env P a b p) : Forces true R env P x z p ∧ Forces true R env P y z p := by
  have hp := ForcingAtomicBasic.condition hM he
  exact ⟨(mem_singleton hM hpre ht htop hb hp).mp
      ((ForcingAtomicLaws.mem_congr_right hM hpre he).mp (mem_pair_left hM hpre ht htop ha hp)),
    (mem_singleton hM hpre ht htop hb hp).mp
      ((ForcingAtomicLaws.mem_congr_right hM hpre he).mp (mem_pair_right hM hpre ht htop ha hp))⟩

theorem eq_pair_cancel_left (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y z a b p : M.Carrier .set} (ha : PairName t x y a) (hb : PairName t x z b)
    (he : Forces true R env P a b p) : Forces true R env P y z p := by
  have hp := ForcingAtomicBasic.condition hM he
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  have hm := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp (mem_pair_right hM hpre ht htop ha hp)
  obtain ⟨r,hr,hrq,h | h⟩ := (ForcingPairUnion.mem_pair hM hb ht htop hp).mp hm q hq hqp
  · obtain ⟨c,hc⟩ := ForcingPairName.exists_pairName hM t x x
    have hs := eq_pair_congr hM hpre ht htop ha hc (ForcingAtomicBasic.eq_refl hM hpre x r hr) h
    have h' := ForcingAtomicLaws.eq_trans hM hpre
      (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hr (hpre.2 r q p hr hq hp hrq hqp) he)) hs
    exact ⟨r,hr,hrq,ForcingAtomicLaws.eq_trans hM hpre h
      (ForcingAtomicBasic.eq_symm hM (eq_pair_singleton hM hpre ht htop hb hc h').2)⟩
  · exact ⟨r,hr,hrq,h⟩

theorem eq_opair_congr (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y x' y' a b p : M.Carrier .set}
    (ha : OrderedPairName t x y a) (hb : OrderedPairName t x' y' b)
    (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p) : Forces true R env P a b p := by
  obtain ⟨a1,a2,h1,h2,ha⟩ := ha
  obtain ⟨b1,b2,k1,k2,hb⟩ := hb
  exact eq_pair_congr hM hpre ht htop ha hb
    (eq_pair_congr hM hpre ht htop h1 k1 hx hx)
    (eq_pair_congr hM hpre ht htop h2 k2 hx hy)

theorem eq_opair_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    {x y x' y' a b p : M.Carrier .set}
    (ha : OrderedPairName t x y a) (hb : OrderedPairName t x' y' b) :
    Forces true R env P a b p ↔ Forces true R env P x x' p ∧ Forces true R env P y y' p := by
  constructor
  · intro he
    have hp := ForcingAtomicBasic.condition hM he
    obtain ⟨a1,a2,h1,h2,hA⟩ := ha
    obtain ⟨b1,b2,k1,k2,hB⟩ := hb
    have hx : Forces true R env P x x' p := by
      apply ForcingAtomicBasic.eq_of_dense hM hpre hp
      intro q hq hqp
      have hm := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp (mem_pair_left hM hpre ht htop hA hp)
      obtain ⟨r,hr,hrq,h | h⟩ := (ForcingPairUnion.mem_pair hM hB ht htop hp).mp hm q hq hqp
      · exact ⟨r,hr,hrq,(eq_pair_singleton hM hpre ht htop h1 k1 h).1⟩
      · exact ⟨r,hr,hrq,ForcingAtomicBasic.eq_symm hM
          (eq_pair_singleton hM hpre ht htop k2 h1 (ForcingAtomicBasic.eq_symm hM h)).1⟩
    refine ⟨hx,?_⟩
    obtain ⟨c,hc⟩ := ForcingPairName.exists_pairName hM t x' y
    obtain ⟨d,hd⟩ := ForcingPairName.exists_pairName hM t b1 c
    have hmid : OrderedPairName t x' y d := ⟨b1,c,k1,hc,hd⟩
    have hm := eq_opair_congr hM hpre ht htop ⟨a1,a2,h1,h2,hA⟩ hmid hx
      (ForcingAtomicBasic.eq_refl hM hpre y p hp)
    have h := ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM hm) he
    exact eq_pair_cancel_left hM hpre ht htop hc k2
      (eq_pair_cancel_left hM hpre ht htop hd hB h)
  · exact fun ⟨hx,hy⟩ => eq_opair_congr hM hpre ht htop ha hb hx hy

def equalitySentence {n : Nat} (R : Formula (n+2)) (P t x y x' y' a b p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem t P).imp
    ((Formula.all ((Formula.mem (Fin.last n) P.castSucc).imp
      (ReplacementPredicates.rel R (ReplacementPredicates.paramsUp id) (Fin.last n) t.castSucc))).imp
    ((ForcingOrderedPairName.orderedPairName t x y a).imp
    ((ForcingOrderedPairName.orderedPairName t x' y' b).imp
    ((ForcingAtomicRelations.forces true R id P a b p).iff
    ((ForcingAtomicRelations.forces true R id P x x' p).conj
      (ForcingAtomicRelations.forces true R id P y y' p)))))))).close

theorem equality_models {n : Nat} (R : Formula (n+2)) (P t x y x' y' a b p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (equalitySentence R P t x y x' y' a b p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre ht htop ha hb
  have htop' : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) → MapRel R env r (env t) := by
    intro r hr
    let v : Fin (n+1) → M.Carrier .set := Fin.lastCases r env
    have hr' : Formula.Realize (fun a b => M.relInterp .membership (.cons a (.cons b .nil)))
        v (.mem (Fin.last n) P.castSucc) := by
      simpa only [v,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc,
        Definitional.Project.FirstOrderSemantics.reduct] using hr
    have hrel := (ForcingMapConditions.rel_semantics (M := M) v R
      (ReplacementPredicates.paramsUp (id : Fin n → Fin n)) (Fin.last n) t.castSucc).mp (htop r hr')
    simpa only [v,ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hrel
  have h := eq_opair_iff hM
    ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) ht htop'
    ((ForcingOrderedPairName.orderedPairName_semantics (M := M) env t x y a).mp ha)
    ((ForcingOrderedPairName.orderedPairName_semantics (M := M) env t x' y' b).mp hb) (p := env p)
  constructor
  · intro he
    obtain ⟨hx,hy⟩ := h.mp ((ForcingAtomicRelations.forces_semantics (M := M) env true R id P a b p).mp he)
    exact ⟨(ForcingAtomicRelations.forces_semantics (M := M) env true R id P x x' p).mpr hx,
      (ForcingAtomicRelations.forces_semantics (M := M) env true R id P y y' p).mpr hy⟩
  · intro he
    exact (ForcingAtomicRelations.forces_semantics (M := M) env true R id P a b p).mpr
      (h.mpr ⟨(ForcingAtomicRelations.forces_semantics (M := M) env true R id P x x' p).mp he.1,
        (ForcingAtomicRelations.forces_semantics (M := M) env true R id P y y' p).mp he.2⟩)

theorem equality_kernel_certificate {n : Nat} (R : Formula (n+2)) (P t x y x' y' a b p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (equalitySentence R P t x y x' y' a b p)) :=
  ModelTransfer.derives (fun _ hM => equality_models R P t x y x' y' a b p hM)

end PPAC.Migration.ForcingOrderedPairForcing
