/- Positive natural scaling of the existing fraction codes. Consumer:
ProbeMargins delta = (exitHeight - floor - K) / 4.
Reuse native multiplication, existing fraction order and scaled_equiv. -/
import PPAC.Migration.ConstructionCutArithmetic

namespace PPAC.Migration.ConstructionFractionScaling
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Times (hM : FirstOrder.Theory.Models M nativeZF) (w n q r : M.Carrier .set) : Prop :=
  ∃ a b an, Coordinates w q a b ∧ Mul hM a n an ∧ Coordinates w r an b

def times {m : Nat} (w n q r : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (coordinates w.succ.succ.succ q.succ.succ.succ 2 1)
    (.conj (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound 0) (.bound 2) (.bound n.succ.succ.succ))
      (coordinates w.succ.succ.succ r.succ.succ.succ 0 1)))))

theorem times_freeClosed {m : Nat} (w n q r : Fin m) : (times w n q r).FreeClosed := by
  simp -implicitDefEqProofs [times,Definitional.Formula.FreeClosed,coordinates_freeClosed]

theorem times_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n q r : Fin m) :
    Project.Formula.satisfies env (times w n q r) ↔ Times hM (env.bound w) (env.bound n) (env.bound q) (env.bound r) := by
  simp only [times,Times,ConstructionFractionOrder.Mul,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinates_semantics hM,Project.Formula.satisfies_isOrdinalMultiplication_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

theorem exists_times (hM : FirstOrder.Theory.Models M nativeZF) {w n q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hq : Fraction w q) : ∃ r, Times hM w n q r := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨an,han,hm⟩ := mul_exists hM hw hq.1 hn
  obtain ⟨r,hr⟩ := KuratowskiZF.exists_code hM an b
  exact ⟨r,a,b,an,hq,hm,han,hq.2.1,hq.2.2.1,hr⟩

theorem times_unique (hM : FirstOrder.Theory.Models M nativeZF) {w n q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hr : Times hM w n q r) (hs : Times hM w n q s) : r = s := by
  obtain ⟨a,b,an,hq,hm,hr⟩ := hr
  obtain ⟨a',b',an',hq',hm',hs⟩ := hs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq.2.2.2 hq'.2.2.2
  have he := mul_unique hM hw hn hm hm'
  subst an'
  exact KuratowskiZF.code_unique hM hr.2.2.2 hs.2.2.2

theorem times_range {hM : FirstOrder.Theory.Models M nativeZF} {w n q r : M.Carrier .set}
    (hr : Times hM w n q r) : Fraction w r := by
  obtain ⟨a,b,an,_,_,hr⟩ := hr
  exact ⟨an,b,hr⟩

theorem order_iff (hM : FirstOrder.Theory.Models M nativeZF) {w n q r t u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z n)
    (ht : Times hM w n q t) (hu : Times hM w n r u) : Le hM w t u ↔ Le hM w q r := by
  obtain ⟨a,b,an,hq,han,ht⟩ := ht
  obtain ⟨c,d,cn,hr,hcn,hu⟩ := hu
  obtain ⟨ad,hadw,had⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨cb,hcbw,hcb⟩ := mul_exists hM hw hr.1 hq.2.1
  obtain ⟨and,_,hand⟩ := mul_exists hM hw ht.1 hr.2.1
  obtain ⟨cnb,_,hcnb⟩ := mul_exists hM hw hu.1 hq.2.1
  obtain ⟨adn,_,hadn⟩ := mul_exists hM hw hadw hn
  obtain ⟨cbn,_,hcbn⟩ := mul_exists hM hw hcbw hn
  have heA := mul_swap hM hw hq.1 hn hr.2.1 han had hand hadn
  have heC := mul_swap hM hw hr.1 hn hq.2.1 hcn hcb hcnb hcbn
  rw [le_iff_products hM hw ht hu hand hcnb,heA,heC]
  exact (mul_le_iff hM hw hn hnp hadw hcbw
    (mul_comm hM hw hadw hn hadn) (mul_comm hM hw hcbw hn hcbn)).trans
    (le_iff_products hM hw hq hr had hcb).symm

theorem strict_iff (hM : FirstOrder.Theory.Models M nativeZF) {w n q r t u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z n)
    (ht : Times hM w n q t) (hu : Times hM w n r u) : Lt hM w t u ↔ Lt hM w q r :=
  and_congr (order_iff hM hw hn hnp ht hu) (not_congr (order_iff hM hw hn hnp hu ht))

/-- Divide the denominator, then use the already proved scaled_equiv.
Surjectivity is by value; fraction code equality is not incorrectly required. -/
theorem inverse_value (hM : FirstOrder.Theory.Models M nativeZF) {w n r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z n)
    (hr : Fraction w r) : ∃ q t, Fraction w q ∧ Times hM w n q t ∧ Le hM w t r ∧ Le hM w r t := by
  obtain ⟨a,b,hr⟩ := hr
  obtain ⟨bn,hbnw,hbn⟩ := mul_exists hM hw hr.2.1 hn
  have hbnPos := ConstructionFractionAddition.mul_nonempty hM hw hr.2.1 hn hr.2.2.1 hnp hbn
  obtain ⟨an,hanw,han⟩ := mul_exists hM hw hr.1 hn
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM a bn
  obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM an bn
  have hqC : Coordinates w q a bn := ⟨hr.1,hbnw,hbnPos,hq⟩
  have htC : Coordinates w t an bn := ⟨hanw,hbnw,hbnPos,ht⟩
  have he := ConstructionFractionDifference.scaled_equiv hM hw hr htC hn han hbn
  exact ⟨q,t,⟨a,bn,hqC⟩,⟨a,bn,an,hqC,han,htC⟩,he.2,he.1⟩

end PPAC.Migration.ConstructionFractionScaling
