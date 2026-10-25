/- Pinned AtomicForcing.edge_map_orderIso / atomic_symmetry (lines 406-487).
Actual main-route consumer: SymmetricNames.forces_symmetry. Conditions and
names move together. No generic filter or quotient truth lemma is used. -/
import PPAC.Migration.ForcingAtomicLaws
import PPAC.Migration.ForcingConditionAction

namespace PPAC.Migration.ForcingAtomicSymmetry
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel IsFunction Mapped mapping)
open ForcingAtomicRelations (Forces forces EqHalf)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Relational presentation of the source injective map and condition order isomorphism. -/
def Transport {n : Nat} (f R : Formula (n+2)) (v : Fin n → M.Carrier .set) (P : M.Carrier .set) : Prop :=
  IsFunction f v ∧
  (∀ x y z, MapRel f v x z → MapRel f v y z → x = y) ∧
  (∀ x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P → MapRel f v x y →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y P) ∧
  (∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
    ∃ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ MapRel f v x y) ∧
  (∀ x y a b, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y P → MapRel f v x a → MapRel f v y b →
    (MapRel R v a b ↔ MapRel R v x y))

def transport {n m : Nat} (f R : Formula (n+2)) (rho : Fin n → Fin m) (P : Fin m) : Formula m :=
  let u2 : Fin m → Fin (m+2) := fun i => i.castSucc.castSucc
  let u3 : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let u4 : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let x2 := (Fin.last m).castSucc
  let y2 := Fin.last (m+1)
  let x3 := (Fin.last m).castSucc.castSucc
  let y3 := (Fin.last (m+1)).castSucc
  let z3 := Fin.last (m+2)
  let x4 := (Fin.last m).castSucc.castSucc.castSucc
  let y4 := (Fin.last (m+1)).castSucc.castSucc
  let a4 := (Fin.last (m+2)).castSucc
  let b4 := Fin.last (m+3)
  (ForcingMapConditions.function f rho).conj
    ((Formula.all (.all (.all ((ReplacementPredicates.rel f (fun i => u3 (rho i)) x3 z3).imp
      ((ReplacementPredicates.rel f (fun i => u3 (rho i)) y3 z3).imp (.equal x3 y3)))))).conj
    ((Formula.all (.all ((Formula.mem x2 (u2 P)).imp
      ((ReplacementPredicates.rel f (fun i => u2 (rho i)) x2 y2).imp (.mem y2 (u2 P)))))).conj
    ((Formula.all ((Formula.mem (Fin.last m) P.castSucc).imp (.ex
      ((Formula.mem y2 (u2 P)).conj (ReplacementPredicates.rel f (fun i => u2 (rho i)) y2 x2))))).conj
    (Formula.all (.all (.all (.all ((Formula.mem x4 (u4 P)).imp ((Formula.mem y4 (u4 P)).imp
      ((ReplacementPredicates.rel f (fun i => u4 (rho i)) x4 a4).imp
      ((ReplacementPredicates.rel f (fun i => u4 (rho i)) y4 b4).imp
      ((ReplacementPredicates.rel R (fun i => u4 (rho i)) a4 b4).iff
        (ReplacementPredicates.rel R (fun i => u4 (rho i)) x4 y4)))))))))))))

theorem transport_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f R : Formula (n+2))
    (rho : Fin n → Fin m) (P : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (transport f R rho P) ↔
      Transport f R (fun i => v (rho i)) (v P) := by
  simp only [transport,Transport,Source.Formula.iff,Formula.Realize,ForcingMapConditions.function_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · rintro ⟨hf,hi,hin,hon,ho⟩
    exact ⟨hf,hi,hin,hon,fun x y a b hx hy hxa hyb => ⟨(ho x y a b hx hy hxa hyb).1,(ho x y a b hx hy hxa hyb).2⟩⟩
  · rintro ⟨hf,hi,hin,hon,ho⟩
    exact ⟨hf,hi,hin,hon,fun x y a b hx hy hxa hyb => ⟨(ho x y a b hx hy hxa hyb).mp,(ho x y a b hx hy hxa hyb).mpr⟩⟩

theorem edge_map (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f R : Formula (n+2)} {v : Fin n → M.Carrier .set} {P : M.Carrier .set}
    (ht : Transport f R v P) {a a' nu r r' : M.Carrier .set}
    (ha : Mapped f v a a') (hr : MapRel f v r r') :
    PureKuratowski.PairMember M nu r' a' ↔
      ∃ child, PureKuratowski.PairMember M child r a ∧ Mapped f v child nu := by
  constructor
  · intro he
    obtain ⟨child,s,he,hc,hs⟩ := (ForcingMapConditions.edge_mapping hM ht.1 ha nu r').mp he
    have hsr := ht.2.1 s r r' hs hr
    subst s
    exact ⟨child,he,hc⟩
  · rintro ⟨child,he,hc⟩
    exact (ForcingMapConditions.edge_mapping hM ht.1 ha nu r').mpr ⟨child,r,he,hc,hr⟩

/-- The source membership branches, with the recursive equality query explicit. -/
theorem mem_transport (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f R : Formula (n+2)} {v : Fin n → M.Carrier .set} {P a b a' b' p p' : M.Carrier .set}
    (ht : Transport f R v P) (_ha : Mapped f v a a') (hb : Mapped f v b b')
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hpp : MapRel f v p p')
    (ih : ∀ nu r, PureKuratowski.PairMember M nu r b → ∀ nu' s s', Mapped f v nu nu' →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem s P → MapRel f v s s' →
      (Forces true R v P a nu s ↔ Forces true R v P a' nu' s')) :
    Forces false R v P a b p ↔ Forces false R v P a' b' p' := by
  have hin := ht.2.2.1
  have hon := ht.2.2.2.1
  have hord := ht.2.2.2.2
  constructor
  · intro hm
    apply (ForcingAtomicRelations.mem_iff hM R v P a' b' p').mpr
    refine ⟨hin p p' hp hpp,?_⟩
    intro q' hq' hqp'
    obtain ⟨q,hq,hqq⟩ := hon q' hq'
    obtain ⟨s,nu,r,hs,hsq,hr,he,hsr,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R v P a b p).mp hm).2 q hq ((hord q p q' p' hq hp hqq hpp).mp hqp')
    obtain ⟨s',hss,_⟩ := ht.1 s
    obtain ⟨r',hrr,_⟩ := ht.1 r
    obtain ⟨nu',hnu⟩ := ForcingMapConditions.exists_mapping hM f v ht.1 nu
    exact ⟨s',nu',r',hin s s' hs hss,(hord s q s' q' hs hq hss hqq).mpr hsq,
      hin r r' hr hrr,(edge_map hM ht hb hrr).mpr ⟨nu,he,hnu⟩,
      (hord s r s' r' hs hr hss hrr).mpr hsr,(ih nu r he nu' s s' hnu hs hss).mp heq⟩
  · intro hm
    apply (ForcingAtomicRelations.mem_iff hM R v P a b p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨q',hqq,_⟩ := ht.1 q
    obtain ⟨s',nu',r',hs',hsq',hr',he',hsr',heq'⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R v P a' b' p').mp hm).2 q' (hin q q' hq hqq)
        ((hord q p q' p' hq hp hqq hpp).mpr hqp)
    obtain ⟨s,hs,hss⟩ := hon s' hs'
    obtain ⟨r,hr,hrr⟩ := hon r' hr'
    obtain ⟨nu,he,hnu⟩ := (edge_map hM ht hb hrr).mp he'
    exact ⟨s,nu,r,hs,(hord s q s' q' hs hq hss hqq).mp hsq',hr,he,
      (hord s r s' r' hs hr hss hrr).mp hsr',(ih nu r he nu' s s' hnu hs hss).mpr heq'⟩

/-- One equality half; the two source child orientations supply its premise. -/
theorem half_transport (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f R : Formula (n+2)} {v : Fin n → M.Carrier .set} {P a b a' b' p p' : M.Carrier .set}
    (ht : Transport f R v P) (ha : Mapped f v a a') (_hb : Mapped f v b b')
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hpp : MapRel f v p p')
    (ih : ∀ nu r, PureKuratowski.PairMember M nu r a → ∀ nu' q q', Mapped f v nu nu' →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel f v q q' →
      (Forces false R v P nu b q ↔ Forces false R v P nu' b' q')) :
    EqHalf R v P a b p ↔ EqHalf R v P a' b' p' := by
  have hin := ht.2.2.1
  have hon := ht.2.2.2.1
  have hord := ht.2.2.2.2
  constructor
  · intro h nu' r' hr' he' q' hq' hqp' hqr'
    obtain ⟨r,hr,hrr⟩ := hon r' hr'
    obtain ⟨q,hq,hqq⟩ := hon q' hq'
    obtain ⟨nu,he,hnu⟩ := (edge_map hM ht ha hrr).mp he'
    exact (ih nu r he nu' q q' hnu hq hqq).mp
      (h nu r hr he q hq ((hord q p q' p' hq hp hqq hpp).mp hqp')
        ((hord q r q' r' hq hr hqq hrr).mp hqr'))
  · intro h nu r hr he q hq hqp hqr
    obtain ⟨q',hqq,_⟩ := ht.1 q
    obtain ⟨r',hrr,_⟩ := ht.1 r
    obtain ⟨nu',hnu⟩ := ForcingMapConditions.exists_mapping hM f v ht.1 nu
    exact (ih nu r he nu' q q' hnu hq hqq).mpr
      (h nu' r' (hin r r' hr hrr) ((edge_map hM ht ha hrr).mpr ⟨nu,he,hnu⟩) q' (hin q q' hq hqq)
        ((hord q p q' p' hq hp hqq hpp).mpr hqp) ((hord q r q' r' hq hr hqq hrr).mpr hqr))

def symmetry {n m : Nat} (f R : Formula (n+2)) (rho : Fin n → Fin m) (P a b : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let rr := fun i => up (rho i)
  let aa := (Fin.last m).castSucc.castSucc.castSucc
  let bb := (Fin.last (m+1)).castSucc.castSucc
  let p := (Fin.last (m+2)).castSucc
  let pp := Fin.last (m+3)
  .all (.all (.all (.all ((mapping f rr (up a) aa).imp ((mapping f rr (up b) bb).imp
    ((Formula.mem p (up P)).imp ((ReplacementPredicates.rel f rr p pp).imp
      (((forces false R rr (up P) (up a) (up b) p).iff (forces false R rr (up P) aa bb pp)).conj
        ((forces true R rr (up P) (up a) (up b) p).iff (forces true R rr (up P) aa bb pp))))))))))

def Symmetry {n : Nat} (f R : Formula (n+2)) (v : Fin n → M.Carrier .set) (P a b : M.Carrier .set) : Prop :=
  ∀ a' b' p p', Mapped f v a a' → Mapped f v b b' →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P → MapRel f v p p' →
    (Forces false R v P a b p ↔ Forces false R v P a' b' p') ∧
    (Forces true R v P a b p ↔ Forces true R v P a' b' p')

theorem symmetry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (f R : Formula (n+2))
    (rho : Fin n → Fin m) (P a b : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (symmetry f R rho P a b) ↔
      Symmetry f R (fun i => v (rho i)) (v P) (v a) (v b) := by
  simp only [symmetry,Symmetry,Source.Formula.iff,Formula.Realize,ForcingMapConditions.mapping_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h a b p q ha hb hp hq
    exact ⟨⟨(h a b p q ha hb hp hq).1.1,(h a b p q ha hb hp hq).1.2⟩,
      ⟨(h a b p q ha hb hp hq).2.1,(h a b p q ha hb hp hq).2.2⟩⟩
  · intro h a b p q ha hb hp hq
    exact ⟨⟨(h a b p q ha hb hp hq).1.mp,(h a b p q ha hb hp hq).1.mpr⟩,
      ⟨(h a b p q ha hb hp hq).2.mp,(h a b p q ha hb hp hq).2.mpr⟩⟩

theorem atomic_symmetry (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (f R : Formula (n+2)) (v : Fin n → M.Carrier .set) (P : M.Carrier .set)
    (ht : Transport f R v P) : ∀ a b, Symmetry f R v P a b := by
  let matrix := symmetry f R (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases P v
  have hm : ∀ a b, MapRel matrix inputs a b ↔ Symmetry f R v P a b := by
    intro a b
    have h := symmetry_semantics (M := M) (Fin.lastCases b (Fin.lastCases a inputs)) f R
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc
      (Fin.last (n+1)).castSucc (Fin.last (n+2))
    simpa only [MapRel,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using h
  have all := ForcingPairInduction.formula_induction hM matrix inputs (by
    intro a b il ir isw
    apply (hm a b).mpr
    intro a' b' p p' ha hb hp hpp
    have hl := half_transport hM ht ha hb hp hpp (fun nu r he nu' q q' hnu hq hqq =>
      ((hm nu b).mp (il nu r he) nu' b' q q' hnu hb hq hqq).1)
    have hr := half_transport hM ht hb ha hp hpp (fun nu r he nu' q q' hnu hq hqq =>
      ((hm nu a).mp (isw nu r he) nu' a' q q' hnu ha hq hqq).1)
    refine ⟨mem_transport hM ht ha hb hp hpp (fun nu r he nu' s s' hnu hs hss =>
      ((hm a nu).mp (ir nu r he) a' nu' s s' ha hnu hs hss).2),?_⟩
    constructor
    · intro h
      obtain ⟨_,h1,h2⟩ := (ForcingAtomicRelations.eq_iff hM R v P a b p).mp h
      exact (ForcingAtomicRelations.eq_iff hM R v P a' b' p').mpr ⟨ht.2.2.1 p p' hp hpp,hl.mp h1,hr.mp h2⟩
    · intro h
      obtain ⟨_,h1,h2⟩ := (ForcingAtomicRelations.eq_iff hM R v P a' b' p').mp h
      exact (ForcingAtomicRelations.eq_iff hM R v P a b p).mpr ⟨hp,hl.mpr h1,hr.mpr h2⟩)
  exact fun a b => (hm a b).mp (all a b)

def sentence {n : Nat} (f R : Formula (n+2)) (P a b : Fin n) : Source.Sentence :=
  ((transport f R id P).imp (symmetry f R id P a b)).close

theorem models {n : Nat} (f R : Formula (n+2)) (P a b : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence f R P a b)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v ht
  exact (symmetry_semantics (M := M) v f R id P a b).mpr
    (atomic_symmetry hM f R v (v P) ((transport_semantics (M := M) v f R id P).mp ht) (v a) (v b))

theorem kernel_certificate {n : Nat} (f R : Formula (n+2)) (P a b : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence f R P a b)) :=
  ModelTransfer.derives (fun _ hM => models f R P a b hM)

/-- Only the order on P is constrained, as in the original P order isomorphism. -/
def orderOn {n : Nat} (R : Formula (n+2)) (P r : Fin n) : Formula n :=
  let up : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let x := (Fin.last n).castSucc.castSucc.castSucc
  let y := (Fin.last (n+1)).castSucc.castSucc
  let a := (Fin.last (n+2)).castSucc
  let b := Fin.last (n+3)
  .all (.all (.all (.all ((Formula.mem x (up P)).imp ((Formula.mem y (up P)).imp
    ((ForcingConditionAction.act (up P) (up r) x a).imp
    ((ForcingConditionAction.act (up P) (up r) y b).imp
    ((ReplacementPredicates.rel R up a b).iff (ReplacementPredicates.rel R up x y)))))))))

def OrderOn {n : Nat} (R : Formula (n+2)) (v : Fin n → M.Carrier .set) (P r : M.Carrier .set) : Prop :=
  ∀ x y a b, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
    ForcingConditionAction.Act P r x a → ForcingConditionAction.Act P r y b →
    (MapRel R v a b ↔ MapRel R v x y)

theorem orderOn_semantics {n : Nat} (v : Fin n → M.Carrier .set) (R : Formula (n+2)) (P r : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (orderOn R P r) ↔
      OrderOn R v (v P) (v r) := by
  simp only [orderOn,OrderOn,Source.Formula.iff,Formula.Realize,ForcingConditionAction.act_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h x y a b hx hy hxa hyb
    exact ⟨(h x y a b hx hy hxa hyb).1,(h x y a b hx hy hxa hyb).2⟩
  · intro h x y a b hx hy hxa hyb
    exact ⟨(h x y a b hx hy hxa hyb).mp,(h x y a b hx hy hxa hyb).mpr⟩

/-- Discharge the map hypotheses for the already constructed literal actCode. -/
theorem action_transport {n : Nat} (R : Formula (n+2)) (v : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : ForcingConditionGraphs.Permutation (v P) (v r)) (ho : OrderOn R v (v P) (v r)) :
    Transport (ForcingConditionAction.actFormula P r) R v (v P) := by
  refine ⟨ForcingConditionAction.act_function v P r hr.1,?_,?_,?_,?_⟩
  · intro x y z hx hy
    have hx' := (ForcingConditionAction.relation_semantics v P r x z).mp hx
    have hy' := (ForcingConditionAction.relation_semantics v P r y z).mp hy
    rcases hx' with ⟨_,hxe⟩ | ⟨hnx,hxz⟩
    · rcases hy' with ⟨_,hye⟩ | ⟨hny,hyz⟩
      · exact hr.2.1 x y z hxe hye
      · exact False.elim (hny (hyz.symm ▸ hr.1.2 x z hxe))
    · rcases hy' with ⟨_,hye⟩ | ⟨_,hyz⟩
      · exact False.elim (hnx (hxz.symm ▸ hr.1.2 y z hye))
      · exact hxz.trans hyz.symm
  · intro x y hx hxy
    exact ForcingConditionAction.act_into hr.1 hx ((ForcingConditionAction.relation_semantics v P r x y).mp hxy)
  · intro y hy
    obtain ⟨x,hx,he⟩ := hr.2.2 y hy
    exact ⟨x,hx,(ForcingConditionAction.relation_semantics v P r x y).mpr (Or.inl ⟨hx,he⟩)⟩
  · intro x y a b hx hy hxa hyb
    exact ho x y a b hx hy ((ForcingConditionAction.relation_semantics v P r x a).mp hxa)
      ((ForcingConditionAction.relation_semantics v P r y b).mp hyb)

def actionSentence {n : Nat} (R : Formula (n+2)) (P r a b : Fin n) : Source.Sentence :=
  ((ForcingConditionGraphs.permutation P r).imp ((orderOn R P r).imp
    (symmetry (ForcingConditionAction.actFormula P r) R id P a b))).close

theorem action_models {n : Nat} (R : Formula (n+2)) (P r a b : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (actionSentence R P r a b)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr ho
  exact (symmetry_semantics (M := M) v (ForcingConditionAction.actFormula P r) R id P a b).mpr
    (atomic_symmetry hM (ForcingConditionAction.actFormula P r) R v (v P)
      (action_transport R v P r ((ForcingConditionGraphs.permutation_semantics (M := M) v P r).mp hr)
        ((orderOn_semantics (M := M) v R P r).mp ho)) (v a) (v b))

theorem action_kernel_certificate {n : Nat} (R : Formula (n+2)) (P r a b : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (actionSentence R P r a b)) :=
  ModelTransfer.derives (fun _ hM => action_models R P r a b hM)

end PPAC.Migration.ForcingAtomicSymmetry
