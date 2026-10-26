/- Positive-natural division of general cuts, needed for the pinned probe
interval delta / 4. Division is an exact inverse image under the existing
fraction scaling; use native Separation and definable-function construction. -/
import PPAC.Migration.ConstructionFractionScaling

namespace PPAC.Migration.ConstructionCutDivision
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionScaling (Times times times_freeClosed times_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF) (w Q n a c : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q c ↔ (Project.FirstOrderSemantics.reduct M).mem q Q ∧
    ∃ r, Times hM w n q r ∧ (Project.FirstOrderSemantics.reduct M).mem r a

def scaledMember {m : Nat} (w n a q : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (times w.succ n.succ q.succ 0) (.mem (.bound 0) (.bound a.succ)))

theorem scaledMember_freeClosed {m : Nat} (w n a q : Fin m) : (scaledMember w n a q).FreeClosed := by
  simp -implicitDefEqProofs [scaledMember,Definitional.Formula.FreeClosed,times_freeClosed]

theorem scaledMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n a q : Fin m) :
    Project.Formula.satisfies env (scaledMember w n a q) ↔ ∃ r,
      Times hM (env.bound w) (env.bound n) (env.bound q) r ∧ (Project.FirstOrderSemantics.reduct M).mem r (env.bound a) := by
  simp only [scaledMember,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,times_semantics hM]
  rfl

def value {m : Nat} (w Q n a c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound Q.succ)) (scaledMember w.succ n.succ a.succ 0)))

theorem value_freeClosed {m : Nat} (w Q n a c : Fin m) : (value w Q n a c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,scaledMember_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q n a c : Fin m) :
    Project.Formula.satisfies env (value w Q n a c) ↔
      Value hM (env.bound w) (env.bound Q) (env.bound n) (env.bound a) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,scaledMember_semantics hM]
  rfl

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) (w Q n a : M.Carrier .set) :
    ∃ c, Value hM w Q n a c := by
  let schema : Project.UnarySchema 3 := { body := scaledMember 1 2 3 0, freeClosed := scaledMember_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases n (fun _ => a)), free := fun _ => w }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  exact ⟨c,fun q => (hc q).trans (and_congr_right (fun _ => scaledMember_semantics hM (env.push q) 1 2 3 0))⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q n a c d : M.Carrier .set}
    (hc : Value hM w Q n a c) (hd : Value hM w Q n a d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun q => (hc q).trans (hd q).symm)

section Positive
variable {hM : FirstOrder.Theory.Models M nativeZF} {w Q n : M.Carrier .set}
variable (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
variable (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
variable (hnp : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z n)
include hw hQ hn hnp

theorem value_cut {a c : M.Carrier .set} (ha : Cut hM w Q a) (hc : Value hM w Q n a c) : Cut hM w Q c := by
  refine ⟨fun q hq => ((hc q).mp hq).1,?_,?_,?_⟩
  · intro p q hq hpq
    obtain ⟨_,r,hr,hra⟩ := (hc q).mp hq
    have hpqCopy := hpq
    obtain ⟨i,j,k,l,hp,_,_⟩ := hpqCopy
    obtain ⟨t,ht⟩ := ConstructionFractionScaling.exists_times hM hw hn ⟨i,j,hp⟩
    have htr := (ConstructionFractionScaling.order_iff hM hw hn hnp ht hr).mpr hpq
    exact (hc p).mpr ⟨(hQ p).mpr ⟨i,j,hp⟩,t,ht,ha.2.1 t r hra htr⟩
  · intro q hq
    obtain ⟨_,r,hr,hra⟩ := (hc q).mp hq
    obtain ⟨s,hsa,hrs⟩ := ha.2.2.1 r hra
    obtain ⟨p,t,hp,ht,hts,hst⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ s).mp (ha.1 s hsa))
    have hpa := (hc p).mpr ⟨(hQ p).mpr hp,t,ht,ha.2.1 t s hsa hts⟩
    exact ⟨p,hpa,(ConstructionFractionScaling.strict_iff hM hw hn hnp hr ht).mp (lt_le_trans hM hw hrs hst)⟩
  · obtain ⟨s,hs,hsn⟩ := ha.2.2.2
    obtain ⟨q,t,hq,ht,_,hst⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ s).mp hs)
    refine ⟨q,(hQ q).mpr hq,fun hqc => ?_⟩
    obtain ⟨_,r,hr,hra⟩ := (hc q).mp hqc
    have he := ConstructionFractionScaling.times_unique hM hw hn ht hr
    exact hsn (ha.2.1 s r hra (he ▸ hst))

theorem nonempty_iff {a c : M.Carrier .set} (ha : Cut hM w Q a) (hc : Value hM w Q n a c) :
    (∃ q, (Project.FirstOrderSemantics.reduct M).mem q c) ↔ ∃ r, (Project.FirstOrderSemantics.reduct M).mem r a := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨_,r,_,hra⟩ := (hc q).mp hq
    exact ⟨r,hra⟩
  · rintro ⟨r,hr⟩
    obtain ⟨q,t,hq,ht,htr,_⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ r).mp (ha.1 r hr))
    exact ⟨q,(hc q).mpr ⟨(hQ q).mpr hq,t,ht,ha.2.1 t r hr htr⟩⟩

theorem order_iff {a b c d : M.Carrier .set}
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value hM w Q n a c) (hd : Value hM w Q n b d) :
    Subset c d ↔ Subset a b := by
  constructor
  · intro hsub p hp
    obtain ⟨q,t,hq,ht,htp,hpt⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ p).mp (ha.1 p hp))
    have hqc := (hc q).mpr ⟨(hQ q).mpr hq,t,ht,ha.2.1 t p hp htp⟩
    obtain ⟨_,r,hr,hrb⟩ := (hd q).mp (hsub q hqc)
    have he := ConstructionFractionScaling.times_unique hM hw hn ht hr
    exact hb.2.1 p r hrb (he ▸ hpt)
  · intro hsub q hq
    obtain ⟨hqQ,r,hr,hra⟩ := (hc q).mp hq
    exact (hd q).mpr ⟨hqQ,r,hr,hsub r hra⟩

theorem strict_iff {a b c d : M.Carrier .set}
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value hM w Q n a c) (hd : Value hM w Q n b d) :
    (Subset c d ∧ ¬ Subset d c) ↔ (Subset a b ∧ ¬ Subset b a) :=
  and_congr (order_iff hw hQ hn hnp ha hb hc hd) (not_congr (order_iff hw hQ hn hnp hb ha hd hc))

end Positive

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (w Q n R F : M.Carrier .set) : Prop := ∀ a c,
  PureKuratowski.PairMember M a c F ↔ (Project.FirstOrderSemantics.reduct M).mem a R ∧ Value hM w Q n a c

def Laws (F : M.Carrier .set) : Prop :=
  (∀ a c, PureKuratowski.PairMember M a c F →
    ((∃ q, (Project.FirstOrderSemantics.reduct M).mem q c) ↔ ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a)) ∧
  (∀ a b c d, PureKuratowski.PairMember M a c F → PureKuratowski.PairMember M b d F →
    ((Subset c d ↔ Subset a b) ∧ ((Subset c d ∧ ¬ Subset d c) ↔ (Subset a b ∧ ¬ Subset b a))))

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {w Q n R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z n) (hR : CutCarrier hM w Q R) :
    ∃ F, MapsTo R R F ∧ Graph hM w Q n R F ∧ Laws F := by
  let schema : Project.BinarySchema 3 := { body := value 2 3 4 1 0, freeClosed := value_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases Q (fun _ => n)), free := fun _ => w }
  have he (a c : M.Carrier .set) : schema.denote env a c ↔ Value hM w Q n a c :=
    value_semantics hM ((env.push a).push c) 2 3 4 1 0
  obtain ⟨F,hF,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := R) (target := R) (by
      intro a _
      obtain ⟨c,hc⟩ := exists_value hM w Q n a
      exact ⟨c,(he a c).mpr hc⟩) (by
      intro a _ c d hc hd
      exact value_unique hM ((he a c).mp hc) ((he a d).mp hd)) (by
      intro a c ha hc
      exact (hR c).mpr (value_cut hw hQ hn hnp ((hR a).mp ha) ((he a c).mp hc)))
  have hGraph : Graph hM w Q n R F := fun a c => (hg a c).trans (and_congr_right (fun _ => he a c))
  refine ⟨F,(ForcingSupportSize.native_mapsTo hM R R F).mpr hF,hGraph,?_,?_⟩
  · intro a c hc
    obtain ⟨ha,hc⟩ := (hGraph a c).mp hc
    exact nonempty_iff hw hQ hn hnp ((hR a).mp ha) hc
  · intro a b c d hc hd
    obtain ⟨ha,hc⟩ := (hGraph a c).mp hc
    obtain ⟨hb,hd⟩ := (hGraph b d).mp hd
    exact ⟨order_iff hw hQ hn hnp ((hR a).mp ha) ((hR b).mp hb) hc hd,
      strict_iff hw hQ hn hnp ((hR a).mp ha) ((hR b).mp hb) hc hd⟩

theorem exists_quarter (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) :
    ∃ one two three four F, ConstructionBaseWeights.Digits w one two three ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf four three ∧
      (Project.FirstOrderSemantics.reduct M).mem four w ∧ MapsTo R R F ∧ Graph hM w Q four R F ∧ Laws F := by
  obtain ⟨one,two,three,hd⟩ := ConstructionBaseWeights.digits_exists hw
  obtain ⟨four,hfour,hfw⟩ := hw.1.2 three hd.2.2.1
  obtain ⟨F,hF,hGraph,hLaws⟩ := exists_graph hM hw hQ hfw ⟨three,hfour.predecessor_mem⟩ hR
  exact ⟨one,two,three,four,F,hd,hfour,hfw,hF,hGraph,hLaws⟩

end PPAC.Migration.ConstructionCutDivision
