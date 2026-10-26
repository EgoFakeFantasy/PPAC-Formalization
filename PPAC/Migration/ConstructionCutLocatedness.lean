/- Internal cut-boundary approximation needed for the pinned ProbeMargins
nonnegative differences. The first omitted grid index is obtained from
native Foundation on a separated subset of internal omega, never from an
external least-number search or an external well-foundedness assumption. -/
import PPAC.Migration.ConstructionCutAssociativity

namespace PPAC.Migration.ConstructionCutLocatedness
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- A zero numerator represents a least fraction for any positive denominator. -/
theorem empty_le (hM : FirstOrder.Theory.Models M nativeZF) {w z q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hz : Coordinates w z a b)
    (ha : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x a) (hq : Fraction w q) : Le hM w z q := by
  obtain ⟨c,d,hq⟩ := hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  have had : Mul hM a d a := mul_comm hM hw hq.2.1 hz.1
    ((ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
      (hw.members_areOrdinals hZF d hq.2.1) ha).mpr ha)
  obtain ⟨cb,hCb,hcb⟩ := mul_exists hM hw hq.1 hz.2.1
  have hle : NatLe a cb := by
    rcases nat_compare hM hw hz.1 hCb with he | hlt | hlt
    · exact Or.inl he
    · exact Or.inr hlt
    · exact (ha cb hlt).elim
  exact (le_iff_products hM hw hz hq had hcb).mpr hle

def badIndex {m : Nat} (w n a k : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (coordinates w.succ 0 k.succ n.succ) (.neg (.mem (.bound 0) (.bound a.succ))))

theorem badIndex_freeClosed {m : Nat} (w n a k : Fin m) : (badIndex w n a k).FreeClosed := by
  simp -implicitDefEqProofs [badIndex,Definitional.Formula.FreeClosed,coordinates_freeClosed]

theorem badIndex_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w n a k : Fin m) : Project.Formula.satisfies env (badIndex w n a k) ↔
    ∃ q, Coordinates (env.bound w) q (env.bound k) (env.bound n) ∧
      ¬ (Project.FirstOrderSemantics.reduct M).mem q (env.bound a) := by
  simp only [badIndex,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinates_semantics hM,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  rfl

/-- An internal unit grid crosses every nonempty proper cut in one step. -/
theorem grid_boundary (hM : FirstOrder.Theory.Models M nativeZF) {w Q a n one step : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hNonempty : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q a)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hstep : Coordinates w step one n) : ∃ q s,
      (Project.FirstOrderSemantics.reduct M).mem q a ∧
      ¬ (Project.FirstOrderSemantics.reduct M).mem s a ∧ Sum hM w q step s := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  let schema : Project.UnarySchema 3 := {
    body := badIndex 1 2 3 0
    freeClosed := badIndex_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases n (fun _ => a)), free := fun _ => w }
  obtain ⟨bad,hBad⟩ := ZF.separation_exists_d hZF schema env w
  have hBadIff : ∀ k, (Project.FirstOrderSemantics.reduct M).mem k bad ↔
      (Project.FirstOrderSemantics.reduct M).mem k w ∧ ∃ q, Coordinates w q k n ∧
        ¬ (Project.FirstOrderSemantics.reduct M).mem q a := fun k =>
    (hBad k).trans (and_congr_right (fun _ => badIndex_semantics hM (env.push k) 1 2 3 0))
  obtain ⟨r,hrQ,hnr⟩ := ha.2.2.2
  obtain ⟨c,d,hr⟩ := (hQ r).mp hrQ
  obtain ⟨cn,hCn,hcn⟩ := mul_exists hM hw hr.1 hstep.2.1
  obtain ⟨upper,hUpperCode⟩ := KuratowskiZF.exists_code hM cn n
  have hUpper : Coordinates w upper cn n := ⟨hCn,hstep.2.1,hstep.2.2.1,hUpperCode⟩
  obtain ⟨cnd,_,hcnd⟩ := mul_exists hM hw hCn hr.2.1
  have hLe : NatLe cn cnd := ZF.ordinalMultiplication_right_eq_or_mem hZF I
    (ord d hr.2.1) hr.2.2.1 (ord cn hCn) (mul_comm hM hw hCn hr.2.1 hcnd)
  have hrUpper := (le_iff_products hM hw hr hUpper hcn hcnd).mpr hLe
  have hnUpper : ¬ (Project.FirstOrderSemantics.reduct M).mem upper a :=
    fun h => hnr (ha.2.1 r upper h hrUpper)
  obtain ⟨k,hk,hMin⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨cn,(hBadIff cn).mpr ⟨hCn,upper,hUpper,hnUpper⟩⟩
  obtain ⟨hkW,u,hu,hnu⟩ := (hBadIff k).mp hk
  have hkN : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x k := by
    apply Classical.byContradiction
    intro hn
    obtain ⟨p,hpa⟩ := hNonempty
    have hz := empty_le hM hw hu (fun x hx => hn ⟨x,hx⟩) ((hQ p).mp (ha.1 p hpa))
    exact hnu (ha.2.1 u p hpa hz)
  obtain ⟨i,hi,hsucc⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hkW hkN
  obtain ⟨q,hqCode⟩ := KuratowskiZF.exists_code hM i n
  have hq : Coordinates w q i n := ⟨hi,hstep.2.1,hstep.2.2.1,hqCode⟩
  have hqa : (Project.FirstOrderSemantics.reduct M).mem q a := by
    apply Classical.byContradiction
    intro hnq
    exact hMin i ((hBadIff i).mpr ⟨hi,q,hq,hnq⟩) hsucc.predecessor_mem
  obtain ⟨zero,hzero,hOne⟩ := hone
  have hAdd : Add hM i one k := (ZF.ordinalAddition_successor_iff hZF I
    (SetTheory.Structure.IsOrdinal.of_no_members hzero) hOne).mpr
      ⟨i,(ZF.ordinalAddition_zero_iff hZF I hzero).mpr rfl,hsucc⟩
  obtain ⟨s,hs⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨i,n,hq⟩ ⟨one,n,hstep⟩
  have he := ConstructionFractionDifference.same_den_sum hM hw hq hstep hu hAdd hs
  exact ⟨q,s,hqa,fun h => hnu (ha.2.1 u s h he.2),hs⟩

/-- Every positive fraction has a smaller unit step; the denominator is the
successor of its original denominator, using only internal arithmetic. -/
theorem smaller_unit (hM : FirstOrder.Theory.Models M nativeZF) {w delta a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Coordinates w delta a b)
    (ha : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x a) :
    ∃ one n step, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
      Coordinates w step one n ∧ Lt hM w step delta := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨one,hone,ho⟩ := hw.exists_ordinalOne_mem
  obtain ⟨n,hn,hN⟩ := hw.1.2 b hd.2.1
  obtain ⟨step,hStepCode⟩ := KuratowskiZF.exists_code hM one n
  have hstep : Coordinates w step one n := ⟨ho,hN,⟨b,hn.predecessor_mem⟩,hStepCode⟩
  obtain ⟨an,hAn,han⟩ := mul_exists hM hw hd.1 hN
  have hnAn : NatLe n an := ZF.ordinalMultiplication_right_eq_or_mem hZF I (ord a hd.1) ha (ord n hN) han
  have hCross := (mul_one hM hw hd.2.1 ho hone).2
  have hLe : NatLe b an := ZF.eqOrMem_trans (ord an hAn) (Or.inr hn.predecessor_mem) hnAn
  have hNot : ¬ NatLe an b := fun h => nat_not_reverse hM hw hd.2.1
    (ZF.eqOrMem_trans (ord b hd.2.1) hnAn h) hn.predecessor_mem
  exact ⟨one,n,step,hone,hstep,(le_iff_products hM hw hstep hd hCross han).mpr hLe,
    fun h => hNot ((le_iff_products hM hw hd hstep han hCross).mp h)⟩

/-- Actual inside/outside fraction codes separated by less than any prescribed
positive fraction. All indices, the separated bad set and the step are internal. -/
theorem small_boundary (hM : FirstOrder.Theory.Models M nativeZF) {w Q a delta num den : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hNonempty : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q a)
    (hd : Coordinates w delta num den) (hp : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x num) :
    ∃ q step s, (Project.FirstOrderSemantics.reduct M).mem q a ∧
      ¬ (Project.FirstOrderSemantics.reduct M).mem s a ∧ Sum hM w q step s ∧ Lt hM w step delta := by
  obtain ⟨one,n,step,hone,hstep,hlt⟩ := smaller_unit hM hw hd hp
  obtain ⟨q,s,hqa,hnsa,hs⟩ := grid_boundary hM hw hQ ha hNonempty hone hstep
  exact ⟨q,step,s,hqa,hnsa,hs,hlt⟩

end PPAC.Migration.ConstructionCutLocatedness
