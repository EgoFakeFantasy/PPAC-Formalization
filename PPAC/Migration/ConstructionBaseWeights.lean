/- Pinned MonoidBase.Base.height/cost: exact internal natural fraction data.
Reuse the positive-denominator existence/uniqueness argument in the pinned
YesMetaZFC Descriptive/Dyadic donor. Fractions here are pairs of internal
naturals; no identification with a complete real field or margin is claimed. -/
import PPAC.Migration.ConstructionBaseMonoid

namespace PPAC.Migration.ConstructionBaseWeights
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Denominator (hM : FirstOrder.Theory.Models M nativeZF) (w two offset n p : M.Carrier .set) : Prop :=
  ∃ k, (Project.FirstOrderSemantics.reduct M).mem k w ∧
    (Project.FirstOrderSemantics.reduct M).mem p w ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) k n offset ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinalExponentiation (KuratowskiZF.interpretation hM) p two k

def denominator {m : Nat} (w two offset n p : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound w.succ)) (.conj (.mem (.bound p.succ) (.bound w.succ))
    (.conj (Project.Formula.isOrdinalAddition PureKuratowskiProject.convention (.bound 0) (.bound n.succ) (.bound offset.succ))
      (Project.Formula.isOrdinalExponentiation PureKuratowskiProject.convention (.bound p.succ) (.bound two.succ) (.bound 0)))))

theorem denominator_freeClosed {m : Nat} (w two offset n p : Fin m) : (denominator w two offset n p).FreeClosed := by
  simp -implicitDefEqProofs [denominator,Definitional.Formula.FreeClosed]

theorem denominator_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w two offset n p : Fin m) :
    Project.Formula.satisfies env (denominator w two offset n p) ↔
      Denominator hM (env.bound w) (env.bound two) (env.bound offset) (env.bound n) (env.bound p) := by
  simp only [denominator,Denominator,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOrdinalAddition_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOrdinalExponentiation_iff (KuratowskiZF.interpretation hM)
      (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

theorem denominator_exists (hM : FirstOrder.Theory.Models M nativeZF) {w two offset n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) : ∃ p, Denominator hM w two offset n p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨k,hk,_⟩ := ZF.ordinalAddition_existsUnique hZF I n (ord offset ho)
  have hkw := ZF.ordinalAddition_mem_omega hZF I hw hn ho hk
  obtain ⟨p,hp,_⟩ := ZF.ordinalExponentiation_existsUnique hZF I (ord two ht) (ord k hkw)
  exact ⟨p,k,hkw,ZF.ordinalExponentiation_mem_omega hZF I hw ht hkw hp,hk,hp⟩

theorem denominator_unique (hM : FirstOrder.Theory.Models M nativeZF) {w two offset n p q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hp : Denominator hM w two offset n p) (hq : Denominator hM w two offset n q) : p = q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨k,hkw,_,hk,hp⟩ := hp
  obtain ⟨l,_,_,hl,hq⟩ := hq
  have he := ConstructionBaseMonoid.addition_unique hM hw ho hk hl
  subst l
  obtain ⟨r,_,hr⟩ := ZF.ordinalExponentiation_existsUnique hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF two ht) (hw.members_areOrdinals hZF k hkw)
  exact (hr p hp).trans (hr q hq).symm

/-- Donor dyad_denominator_pos_l, with the source shifted exponent retained. -/
theorem denominator_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {w two offset n p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two)
    (hp : Denominator hM w two offset n p) : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a p := by
  obtain ⟨k,hk,_,_,hp⟩ := hp
  have hZF := ModelTransfer.project_models_iff.mp hM
  exact ZF.ordinalExponentiation_isNonemptyOnOrdinals hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF two ht) htn k (hw.members_areOrdinals hZF k hk) p hp

/-- Height uses numerator p-1; cost uses numerator one. -/
def Weight (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (w one two offset n q : M.Carrier .set) : Prop :=
  ∃ p, Denominator hM w two offset n p ∧ ∃ a,
    (Project.FirstOrderSemantics.reduct M).mem a w ∧
    (if height then (Project.FirstOrderSemantics.reduct M).SuccessorOf p a else a = one) ∧
    PureKuratowski.Code M q a p

def weight {m : Nat} (height : Bool) (w one two offset n q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (denominator w.succ.succ two.succ.succ offset.succ.succ n.succ.succ 1)
    (.conj (.mem (.bound 0) (.bound w.succ.succ))
      (.conj (if height then Project.Formula.isSuccessor (.bound 1) (.bound 0)
        else Project.Formula.extensionalEq (.bound 0) (.bound one.succ.succ))
        (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 0) (.bound 1))))))

theorem weight_freeClosed {m : Nat} (height : Bool) (w one two offset n q : Fin m) :
    (weight height w one two offset n q).FreeClosed := by
  cases height <;> simp -implicitDefEqProofs [weight,Definitional.Formula.FreeClosed,
    denominator_freeClosed,PureKuratowskiProject.code]

theorem weight_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (height : Bool) (w one two offset n q : Fin m) :
    Project.Formula.satisfies env (weight height w one two offset n q) ↔
      Weight hM height (env.bound w) (env.bound one) (env.bound two) (env.bound offset) (env.bound n) (env.bound q) := by
  cases height <;> simp only [weight,Weight,Bool.false_eq_true,if_false,if_true,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,denominator_semantics hM,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.code_correct hM,Project.Term.eval_bound] <;>
    exact ⟨fun ⟨p,a,hp,ha,hn,hq⟩ => ⟨p,hp,a,ha,hn,hq⟩,fun ⟨p,hp,a,ha,hn,hq⟩ => ⟨p,a,hp,ha,hn,hq⟩⟩

theorem weight_exists (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    {w one two offset n : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).mem one w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) : ∃ q, Weight hM height w one two offset n q := by
  obtain ⟨p,hp⟩ := denominator_exists hM hw ht ho hn
  cases height
  · obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM one p
    exact ⟨q,p,hp,one,hone,rfl,hq⟩
  · have hpw : (Project.FirstOrderSemantics.reduct M).mem p w := by
      obtain ⟨_,_,hpw,_,_⟩ := hp
      exact hpw
    obtain ⟨a,ha,hpa⟩ := hw.exists_predecessor_of_mem_of_nonempty (ModelTransfer.project_models_iff.mp hM)
      hpw (denominator_nonempty hM hw ht htn hp)
    obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM a p
    exact ⟨q,p,hp,a,ha,hpa,hq⟩

theorem weight_unique (hM : FirstOrder.Theory.Models M nativeZF) {height : Bool}
    {w one two offset n q r : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hq : Weight hM height w one two offset n q) (hr : Weight hM height w one two offset n r) : q = r := by
  obtain ⟨p,hp,a,ha,hpa,hq⟩ := hq
  obtain ⟨p',hp',a',ha',hpa',hr⟩ := hr
  have ep := denominator_unique hM hw ht ho hp hp'
  subst p'
  have ea : a = a' := by
    cases height
    · exact hpa.trans hpa'.symm
    · exact SetTheory.Structure.SuccessorOf.predecessor_eq (ModelTransfer.extensionality hM)
        (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) a ha)
        hpa hpa'
  subst a'
  exact KuratowskiZF.code_unique hM hq hr

def weightSchema (height : Bool) : Project.BinarySchema 4 where
  body := weight height 2 3 4 5 1 0
  freeClosed := weight_freeClosed _ _ _ _ _ _ _

theorem weightSchema_semantics (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4) (n q : M.Carrier .set) :
    (weightSchema height).denote env n q ↔
      Weight hM height (env.bound 0) (env.bound 1) (env.bound 2) (env.bound 3) n q := by
  exact weight_semantics hM ((env.push n).push q) height 2 3 4 5 1 0

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (w one two offset f : M.Carrier .set) : Prop :=
  ∀ n q, PureKuratowski.PairMember M n q f ↔
    (Project.FirstOrderSemantics.reduct M).mem n w ∧ Weight hM height w one two offset n q

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    {w one two offset : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).mem one w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w) : ∃ f, Graph hM height w one two offset f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨pairs,hpairs⟩ := ZF.exists_cartesianProduct hZF I w w
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := Fin.cases w (Fin.cases one (Fin.cases two (fun _ => offset))), free := fun _ => w }
  obtain ⟨f,_,hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I (weightSchema height) env
    (source := w) (target := pairs) (by
      intro n hn
      obtain ⟨q,hq⟩ := weight_exists hM height hw hone ht htn ho hn
      exact ⟨q,(weightSchema_semantics hM height env n q).mpr hq⟩) (by
      intro n _ q r hq hr
      exact weight_unique hM hw ht ho ((weightSchema_semantics hM height env n q).mp hq)
        ((weightSchema_semantics hM height env n r).mp hr)) (by
      intro n q _ hq
      obtain ⟨p,hp,a,ha,_,hq⟩ := (weightSchema_semantics hM height env n q).mp hq
      obtain ⟨_,_,hpw,_,_⟩ := hp
      exact (hpairs q).mpr ⟨a,ha,p,hpw,hq⟩)
  exact ⟨f,fun n q => (hf n q).trans (and_congr Iff.rfl (weightSchema_semantics hM height env n q))⟩

def graph {m : Nat} (height : Bool) (w one two offset f : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff
    (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) 0))
    (.conj (.mem (.bound 1) (.bound w.succ.succ))
      (weight height w.succ.succ one.succ.succ two.succ.succ offset.succ.succ 1 0))))

theorem graph_freeClosed {m : Nat} (height : Bool) (w one two offset f : Fin m) :
    (graph height w one two offset f).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,weight_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (height : Bool) (w one two offset f : Fin m) :
    Project.Formula.satisfies env (graph height w one two offset f) ↔
      Graph hM height (env.bound w) (env.bound one) (env.bound two) (env.bound offset) (env.bound f) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,weight_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Term.eval_bound]
  rfl

def Digits (w one two three : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem one w ∧
  (Project.FirstOrderSemantics.reduct M).mem two w ∧
  (Project.FirstOrderSemantics.reduct M).mem three w ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf two one ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf three two

/-- Donor ds_digits_l extended by the single successor needed for source cost. -/
theorem digits_exists {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ one two three, Digits w one two three := by
  obtain ⟨zero,hz,hzw⟩ := hw.1.1
  obtain ⟨one,hone,how⟩ := hw.1.2 zero hzw
  obtain ⟨two,htwo,htw⟩ := hw.1.2 one how
  obtain ⟨three,hthree,hthw⟩ := hw.1.2 two htw
  exact ⟨one,two,three,how,htw,hthw,⟨zero,hz,hone⟩,htwo,hthree⟩

def digits {m : Nat} (w one two three : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound one) (.bound w)) (.conj (.mem (.bound two) (.bound w))
    (.conj (.mem (.bound three) (.bound w)) (.conj (Project.Formula.isOrdinalOne (.bound one))
      (.conj (Project.Formula.isSuccessor (.bound two) (.bound one))
        (Project.Formula.isSuccessor (.bound three) (.bound two))))))

theorem digits_freeClosed {m : Nat} (w one two three : Fin m) : (digits w one two three).FreeClosed := by
  simp -implicitDefEqProofs [digits,Definitional.Formula.FreeClosed]

theorem digits_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w one two three : Fin m) : Project.Formula.satisfies env (digits w one two three) ↔
      Digits (env.bound w) (env.bound one) (env.bound two) (env.bound three) := by
  simp only [digits,Digits,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound]

theorem graph_total_unique (hM : FirstOrder.Theory.Models M nativeZF) {height : Bool}
    {w one two offset f n : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).mem one w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hf : Graph hM height w one two offset f)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) :
    ∃ q, PureKuratowski.PairMember M n q f ∧ ∀ r, PureKuratowski.PairMember M n r f → r = q := by
  obtain ⟨q,hq⟩ := weight_exists hM height hw hone ht htn ho hn
  exact ⟨q,(hf n q).mpr ⟨hn,hq⟩,fun r hr => weight_unique hM hw ht ho ((hf n r).mp hr).2 hq⟩

theorem exists_weights (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ one two three height cost, Digits w one two three ∧
      Graph hM true w one two one height ∧ Graph hM false w one two three cost := by
  obtain ⟨one,two,three,hd⟩ := digits_exists hw
  have htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two := ⟨one,hd.2.2.2.2.1.predecessor_mem⟩
  obtain ⟨height,hh⟩ := exists_graph hM true hw hd.1 hd.2.1 htn hd.1
  obtain ⟨cost,hc⟩ := exists_graph hM false hw hd.1 hd.2.1 htn hd.2.2.1
  exact ⟨one,two,three,height,cost,hd,hh,hc⟩

/-- The donor exponent comparison turns a positive shifted exponent into p > 1. -/
theorem denominator_above_one (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two offset n p : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hot : (Project.FirstOrderSemantics.reduct M).mem one two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hon : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a offset)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hp : Denominator hM w two offset n p) : (Project.FirstOrderSemantics.reduct M).mem one p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨k,hkw,_,hk,hp⟩ := hp
  have hkn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a k := by
    rcases ZF.ordinalAddition_right_eq_or_mem hZF I (ord n hn) (ord offset ho) hk with he | ho
    · exact he ▸ hon
    · exact ⟨offset,ho⟩
  have honeCopy := hone
  obtain ⟨zero,hz,_⟩ := honeCopy
  have hzk := (ord k hkw).empty_mem_of_nonempty (ZF.modelsKP hZF) hkn hz
  have hpow := (ZF.ordinalExponentiation_zero_iff hZF I (ord two ht) hz).mpr hone
  exact (ZF.ordinalExponentiation_values_mem_iff hZF I (ord two ht) hone hot
    (SetTheory.Structure.IsOrdinal.of_no_members hz) (ord k hkw) hpow hp).mpr hzk

/-- Exact arithmetic guard for a positive natural fraction strictly below one. -/
def ProperFraction (w q : M.Carrier .set) : Prop := ∃ a p,
  (Project.FirstOrderSemantics.reduct M).mem a w ∧ (Project.FirstOrderSemantics.reduct M).mem p w ∧
  PureKuratowski.Code M q a p ∧ (∃ z, (Project.FirstOrderSemantics.reduct M).mem z a) ∧
  (Project.FirstOrderSemantics.reduct M).mem a p

theorem weight_proper (hM : FirstOrder.Theory.Models M nativeZF) {height : Bool}
    {w one two offset n q : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hot : (Project.FirstOrderSemantics.reduct M).mem one two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hon : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a offset)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hq : Weight hM height w one two offset n q) : ProperFraction w q := by
  obtain ⟨p,hp,a,ha,hpa,hq⟩ := hq
  have hop := denominator_above_one hM hw hone ht hot ho hon hn hp
  obtain ⟨_,_,hpw,_,_⟩ := hp
  have hone_nonempty : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := by
    obtain ⟨zero,_,hs⟩ := hone
    exact ⟨zero,hs.predecessor_mem⟩
  refine ⟨a,p,ha,hpw,hq,?_,?_⟩
  · cases height
    · exact hpa.symm ▸ hone_nonempty
    · rcases (hpa one).mp hop with ho | he
      · exact ⟨one,ho⟩
      · exact (ModelTransfer.extensionality hM).eq_of_same_members one a he ▸ hone_nonempty
  · cases height
    · exact hpa.symm ▸ hop
    · exact hpa.predecessor_mem

def properFraction {m : Nat} (w q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ))
    (.conj (.mem (.bound 0) (.bound w.succ.succ))
      (.conj (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 1) (.bound 0))
        (.conj (.existsE (.mem (.bound 0) (.bound 2))) (.mem (.bound 1) (.bound 0)))))))

theorem properFraction_freeClosed {m : Nat} (w q : Fin m) : (properFraction w q).FreeClosed := by
  simp -implicitDefEqProofs [properFraction,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem properFraction_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q : Fin m) :
    Project.Formula.satisfies env (properFraction w q) ↔ ProperFraction (env.bound w) (env.bound q) := by
  simp only [properFraction,ProperFraction,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,KuratowskiZF.code_correct hM,
    Project.Term.eval_bound]
  rfl

def RangeProper (w f : M.Carrier .set) : Prop :=
  ∀ n q, PureKuratowski.PairMember M n q f → ProperFraction w q

def rangeProper {m : Nat} (w f : Fin m) : Project.Formula 1 m := .forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) 0))
  (properFraction w.succ.succ 0)))

theorem rangeProper_freeClosed {m : Nat} (w f : Fin m) : (rangeProper w f).FreeClosed := by
  simp -implicitDefEqProofs [rangeProper,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,properFraction_freeClosed]

theorem rangeProper_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w f : Fin m) :
    Project.Formula.satisfies env (rangeProper w f) ↔ RangeProper (env.bound w) (env.bound f) := by
  simp only [rangeProper,RangeProper,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    properFraction_semantics hM]
  rfl

theorem weights_proper (hM : FirstOrder.Theory.Models M nativeZF) {w one two three height cost : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hh : Graph hM true w one two one height) (hc : Graph hM false w one two three cost) :
    RangeProper w height ∧ RangeProper w cost := by
  have hon : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a one := by
    obtain ⟨zero,_,hs⟩ := hd.2.2.2.1
    exact ⟨zero,hs.predecessor_mem⟩
  constructor
  · intro n q hq
    obtain ⟨hn,hq⟩ := (hh n q).mp hq
    exact weight_proper hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.1 hon hn hq
  · intro n q hq
    obtain ⟨hn,hq⟩ := (hc n q).mp hq
    exact weight_proper hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.2.2.1
      ⟨two,hd.2.2.2.2.2.predecessor_mem⟩ hn hq

/-- Only fraction graphs; it contains no asserted real-field or margin predicate. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.existsE (.existsE
      (.conj (digits (5 : Fin 6) 4 3 2)
        (.conj (graph true (5 : Fin 6) 4 3 4 1)
          (.conj (graph false (5 : Fin 6) 4 3 2 0)
            (.conj (rangeProper (5 : Fin 6) 1) (rangeProper (5 : Fin 6) 0)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,digits_freeClosed,graph_freeClosed,rangeProper_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,digits_semantics,
    graph_semantics hM,rangeProper_semantics hM]
  obtain ⟨one,two,three,height,cost,hd,hh,hc⟩ := exists_weights hM hw
  exact ⟨one,two,three,height,cost,hd,hh,hc,weights_proper hM hw hd hh hc⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionBaseWeights
