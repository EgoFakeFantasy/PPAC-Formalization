/- The bounded cut addition consumed by pinned ProbeMargins cost estimates.
Reuse existing fraction Sum/order and cut Separation. Zero is the empty cut;
the two operand branches retain the exact zero-addition cases. -/
import PPAC.Migration.ConstructionFractionAddition

namespace PPAC.Migration.ConstructionCutAddition
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum sum sum_freeClosed sum_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def SumMember (hM : FirstOrder.Theory.Models M nativeZF) (w a b p : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem p a ∨ (Project.FirstOrderSemantics.reduct M).mem p b ∨
    ∃ q r s, (Project.FirstOrderSemantics.reduct M).mem q a ∧
      (Project.FirstOrderSemantics.reduct M).mem r b ∧ Sum hM w q r s ∧ Le hM w p s

def SumCut (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b c : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p c ↔
    (Project.FirstOrderSemantics.reduct M).mem p Q ∧ SumMember hM w a b p

def AddBound (hM : FirstOrder.Theory.Models M nativeZF) (w a b upper : M.Carrier .set) : Prop :=
  ∀ p, SumMember hM w a b p → (Project.FirstOrderSemantics.reduct M).mem p upper

def sumMember {m : Nat} (w a b p : Fin m) : Project.Formula 1 m :=
  .disj (.mem (.bound p) (.bound a)) (.disj (.mem (.bound p) (.bound b))
    (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound a.succ.succ.succ))
      (.conj (.mem (.bound 1) (.bound b.succ.succ.succ))
        (.conj (sum w.succ.succ.succ 2 1 0) (le w.succ.succ.succ p.succ.succ.succ 0))))))))

theorem sumMember_freeClosed {m : Nat} (w a b p : Fin m) : (sumMember w a b p).FreeClosed := by
  simp -implicitDefEqProofs [sumMember,Definitional.Formula.FreeClosed,sum_freeClosed,le_freeClosed]

theorem sumMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w a b p : Fin m) :
    Project.Formula.satisfies env (sumMember w a b p) ↔
      SumMember hM (env.bound w) (env.bound a) (env.bound b) (env.bound p) := by
  simp only [sumMember,SumMember,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    sum_semantics hM,le_semantics hM]
  rfl

def sumCut {m : Nat} (w Q a b c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound Q.succ)) (sumMember w.succ a.succ b.succ 0)))

theorem sumCut_freeClosed {m : Nat} (w Q a b c : Fin m) : (sumCut w Q a b c).FreeClosed := by
  simp -implicitDefEqProofs [sumCut,Definitional.Formula.FreeClosed,sumMember_freeClosed]

theorem sumCut_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q a b c : Fin m) :
    Project.Formula.satisfies env (sumCut w Q a b c) ↔
      SumCut hM (env.bound w) (env.bound Q) (env.bound a) (env.bound b) (env.bound c) := by
  simp only [sumCut,SumCut,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,sumMember_semantics hM]
  rfl

def addBound {m : Nat} (w a b upper : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (sumMember w.succ a.succ b.succ 0) (.mem (.bound 0) (.bound upper.succ)))

theorem addBound_freeClosed {m : Nat} (w a b upper : Fin m) : (addBound w a b upper).FreeClosed := by
  simp -implicitDefEqProofs [addBound,Definitional.Formula.FreeClosed,sumMember_freeClosed]

theorem addBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w a b upper : Fin m) :
    Project.Formula.satisfies env (addBound w a b upper) ↔
      AddBound hM (env.bound w) (env.bound a) (env.bound b) (env.bound upper) := by
  simp only [addBound,AddBound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,sumMember_semantics hM]
  rfl

theorem sumMember_carrier {hM : FirstOrder.Theory.Models M nativeZF} {w Q a b p : M.Carrier .set}
    (hQ : Carrier w Q) (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hp : SumMember hM w a b p) :
    (Project.FirstOrderSemantics.reduct M).mem p Q := by
  rcases hp with hp | hp | ⟨q,r,s,_,_,_,hq⟩
  · exact ha.1 p hp
  · exact hb.1 p hp
  · obtain ⟨i,j,k,l,hp,_,_⟩ := hq
    exact (hQ p).mpr ⟨i,j,hp⟩

theorem sumMember_lower (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b p t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (ht : SumMember hM w a b t) (hpt : Le hM w p t) :
    SumMember hM w a b p := by
  rcases ht with ht | ht | ⟨q,r,s,hq,hr,hs,hts⟩
  · exact Or.inl (ha.2.1 p t ht hpt)
  · exact Or.inr (Or.inl (hb.2.1 p t ht hpt))
  · exact Or.inr (Or.inr ⟨q,r,s,hq,hr,hs,le_trans hM hw hpt hts⟩)

theorem sumMember_rounded (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hp : SumMember hM w a b p) :
    ∃ t, SumMember hM w a b t ∧ Lt hM w p t := by
  rcases hp with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
  · obtain ⟨t,ht,hpt⟩ := ha.2.2.1 p hp
    exact ⟨t,Or.inl ht,hpt⟩
  · obtain ⟨t,ht,hpt⟩ := hb.2.2.1 p hp
    exact ⟨t,Or.inr (Or.inl ht),hpt⟩
  · obtain ⟨q',hq',hqq'⟩ := ha.2.2.1 q hq
    obtain ⟨t,ht⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ q').mp (ha.1 q' hq')) ((hQ r).mp (hb.1 r hr))
    have hst := (ConstructionFractionAddition.sum_right_lt_iff hM hw hs ht).mpr hqq'
    have htCopy := ht
    obtain ⟨i,j,k,l,n,den,_,_,htc,_⟩ := htCopy
    exact ⟨t,Or.inr (Or.inr ⟨q',r,t,hq',hr,ht,le_refl hM hw ⟨n,den,htc⟩⟩),le_lt_trans hM hw hps hst⟩

theorem exists_sum (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b : M.Carrier .set) :
    ∃ c, SumCut hM w Q a b c := by
  let schema : Project.UnarySchema 3 := {
    body := sumMember 1 2 3 0
    freeClosed := sumMember_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases a (fun _ => b)), free := fun _ => w }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  exact ⟨c,fun p => (hc p).trans (and_congr_right (fun _ => sumMember_semantics hM (env.push p) 1 2 3 0))⟩

theorem sum_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c d : M.Carrier .set}
    (hc : SumCut hM w Q a b c) (hd : SumCut hM w Q a b d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => (hc p).trans (hd p).symm)

theorem bound_mono {hM : FirstOrder.Theory.Models M nativeZF} {w a b c d : M.Carrier .set}
    (h : AddBound hM w a b c) (hcd : Subset c d) : AddBound hM w a b d :=
  fun p hp => hcd p (h p hp)

/-- The relational additive bound is exactly cut inclusion for the actual sum. -/
theorem bound_iff_subset {hM : FirstOrder.Theory.Models M nativeZF} {w Q a b c upper : M.Carrier .set}
    (hQ : Carrier w Q) (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : SumCut hM w Q a b c) :
    AddBound hM w a b upper ↔ Subset c upper := by
  constructor
  · exact fun h p hp => h p ((hc p).mp hp).2
  · exact fun h p hp => h p ((hc p).mpr ⟨sumMember_carrier hQ ha hb hp,hp⟩)

theorem bounded_sum_cut (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c upper : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hu : Cut hM w Q upper)
    (hc : SumCut hM w Q a b c) (hbound : AddBound hM w a b upper) : Cut hM w Q c := by
  refine ⟨fun p hp => ((hc p).mp hp).1,?_,?_,?_⟩
  · intro p t ht hpt
    have hp := sumMember_lower hM hw ha hb ((hc t).mp ht).2 hpt
    exact (hc p).mpr ⟨sumMember_carrier hQ ha hb hp,hp⟩
  · intro p hp
    obtain ⟨t,ht,hpt⟩ := sumMember_rounded hM hw hQ ha hb ((hc p).mp hp).2
    exact ⟨t,(hc t).mpr ⟨sumMember_carrier hQ ha hb ht,ht⟩,hpt⟩
  · obtain ⟨p,hp,hpn⟩ := hu.2.2.2
    exact ⟨p,hp,fun hpc => hpn (hbound p ((hc p).mp hpc).2)⟩

theorem exists_bounded_sum (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b upper : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hu : Cut hM w Q upper)
    (hbound : AddBound hM w a b upper) : ∃ c, Cut hM w Q c ∧ SumCut hM w Q a b c ∧ Subset c upper := by
  obtain ⟨c,hc⟩ := exists_sum hM w Q a b
  exact ⟨c,bounded_sum_cut hM hw hQ ha hb hu hc hbound,hc,(bound_iff_subset hQ ha hb hc).mp hbound⟩

end PPAC.Migration.ConstructionCutAddition
