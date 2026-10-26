/- The fraction multiplication consumed by the pinned rawHeight/rawCost
formulas. Reuse native internal-natural multiplication and its laws;
fraction codes are not quotiented or assumed to be antisymmetric. -/
import PPAC.Migration.ConstructionFractionDifference

namespace PPAC.Migration.ConstructionFractionProduct
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Product (hM : FirstOrder.Theory.Models M nativeZF) (w q r s : M.Carrier .set) : Prop :=
  ∃ a b c d n den, Coordinates w q a b ∧ Coordinates w r c d ∧
    Coordinates w s n den ∧ Mul hM a c n ∧ Mul hM b d den

theorem exists_product (hM : FirstOrder.Theory.Models M nativeZF) {w q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q) (hr : Fraction w r) :
    ∃ s, Product hM w q r s := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨c,d,hr⟩ := hr
  obtain ⟨n,hn,hm⟩ := mul_exists hM hw hq.1 hr.1
  obtain ⟨den,hd,hdm⟩ := mul_exists hM hw hq.2.1 hr.2.1
  obtain ⟨s,hs⟩ := KuratowskiZF.exists_code hM n den
  exact ⟨s,a,b,c,d,n,den,hq,hr,⟨hn,hd,ConstructionFractionAddition.mul_nonempty hM hw
    hq.2.1 hr.2.1 hq.2.2.1 hr.2.2.1 hdm,hs⟩,hm,hdm⟩

theorem product_range {hM : FirstOrder.Theory.Models M nativeZF} {w q r s : M.Carrier .set}
    (hs : Product hM w q r s) : Fraction w s := by
  obtain ⟨a,b,c,d,n,den,_,_,hs,_,_⟩ := hs
  exact ⟨n,den,hs⟩

theorem product_unique (hM : FirstOrder.Theory.Models M nativeZF) {w q r s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q r s) (ht : Product hM w q r t) : s = t := by
  obtain ⟨a,b,c,d,n,den,hq,hr,hs,hn,hd⟩ := hs
  obtain ⟨a',b',c',d',n',den',hq',hr',ht,hn',hd'⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq.2.2.2 hq'.2.2.2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  have en := mul_unique hM hw hr.1 hn hn'
  have ed := mul_unique hM hw hr.2.1 hd hd'
  subst n'; subst den'
  exact KuratowskiZF.code_unique hM hs.2.2.2 ht.2.2.2

theorem product_comm (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q r s) : Product hM w r q s := by
  obtain ⟨a,b,c,d,n,den,hq,hr,hs,hn,hd⟩ := hs
  exact ⟨c,d,a,b,n,den,hr,hq,hs,mul_comm hM hw hq.1 hr.1 hn,
    mul_comm hM hw hq.2.1 hr.2.1 hd⟩

/-- Native natural multiplication, including an empty (zero) factor. -/
theorem nat_mul_mono (hM : FirstOrder.Theory.Models M nativeZF) {w a x y ax ay : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w) (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hax : Mul hM a x ax) (hay : Mul hM a y ay) (hxy : NatLe x y) : NatLe ax ay := by
  classical
  by_cases hn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z a
  · exact (mul_le_iff hM hw ha hn hx hy hax hay).mpr hxy
  · have hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z a := fun z h => hn ⟨z,h⟩
    have hZF := ModelTransfer.project_models_iff.mp hM
    have h0x := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
      (hw.members_areOrdinals hZF x hx) hz).mp (mul_comm hM hw ha hx hax)
    have h0y := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
      (hw.members_areOrdinals hZF y hy) hz).mp (mul_comm hM hw ha hy hay)
    exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members ax ay
      (fun z => ⟨fun h => (h0x z h).elim,fun h => (h0y z h).elim⟩))

/-- (a*b)*(c*d) = (a*c)*(b*d), using only native associativity and the
already accepted three-factor swap. All intermediates remain internal. -/
theorem four_swap (hM : FirstOrder.Theory.Models M nativeZF)
    {w a b c d ab cd ac bd left right : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c w) (hd : (Project.FirstOrderSemantics.reduct M).mem d w)
    (hab : Mul hM a b ab) (hcd : Mul hM c d cd) (hac : Mul hM a c ac) (hbd : Mul hM b d bd)
    (hl : Mul hM ab cd left) (hr : Mul hM ac bd right) : left = right := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have habw := mul_range hM hw ha hb hab
  have hacw := mul_range hM hw ha hc hac
  obtain ⟨abc,habcw,habc⟩ := mul_exists hM hw habw hc
  obtain ⟨acb,_,hacb⟩ := mul_exists hM hw hacw hb
  have he := mul_swap hM hw ha hb hc hab hac habc hacb
  subst acb
  obtain ⟨out,_,hout⟩ := mul_exists hM hw habcw hd
  have hleft := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord ab habw) (ord c hc) (ord d hd) habc hcd hl hout
  have hright := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord ac hacw) (ord b hb) (ord d hd) hacb hbd hr hout
  exact hleft.trans hright.symm

/-- Multiplication by a nonnegative fraction preserves the fraction preorder. -/
theorem product_left_mono (hM : FirstOrder.Theory.Models M nativeZF) {w q r k s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q k s) (ht : Product hM w r k t) (hqr : Le hM w q r) : Le hM w s t := by
  obtain ⟨a,b,c,d,n,den,hq,hk,hs,hn,hd⟩ := hs
  obtain ⟨a',b',c',d',n',den',hr,hk',ht,hn',hd'⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hk.2.2.2 hk'.2.2.2
  obtain ⟨ab',habw,hab⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨a'b,ha'bw,ha'b⟩ := mul_exists hM hw hr.1 hq.2.1
  obtain ⟨cd,hcdw,hcd⟩ := mul_exists hM hw hk.1 hk.2.1
  obtain ⟨l,_,hl⟩ := mul_exists hM hw hs.1 ht.2.1
  obtain ⟨r,_,hr'⟩ := mul_exists hM hw ht.1 hs.2.1
  obtain ⟨l',_,hl'⟩ := mul_exists hM hw habw hcdw
  obtain ⟨r',_,hr''⟩ := mul_exists hM hw ha'bw hcdw
  have el := four_swap hM hw hq.1 hk.1 hr.2.1 hk.2.1 hn hd' hab hcd hl hl'
  have er := four_swap hM hw hr.1 hk.1 hq.2.1 hk.2.1 hn' hd ha'b hcd hr' hr''
  have hNat := (le_iff_products hM hw hq hr hab ha'b).mp hqr
  have hScaled := nat_mul_mono hM hw hcdw habw ha'bw
    (mul_comm hM hw habw hcdw hl') (mul_comm hM hw ha'bw hcdw hr'') hNat
  exact (le_iff_products hM hw hs ht hl hr').mpr (el.symm ▸ er.symm ▸ hScaled)

theorem product_mono (hM : FirstOrder.Theory.Models M nativeZF) {w q r q' r' s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q r s) (ht : Product hM w q' r' t)
    (hq : Le hM w q q') (hr : Le hM w r r') : Le hM w s t := by
  have hqr := hq
  obtain ⟨a,b,c,d,hq',hr',_⟩ := hqr
  obtain ⟨mid,hm⟩ := exists_product hM hw ⟨c,d,hr'⟩ (by
    obtain ⟨a,b,c,d,n,den,_,h,_,_,_⟩ := hs
    exact ⟨c,d,h⟩)
  have hFirst := product_left_mono hM hw hs hm hq
  exact le_trans hM hw hFirst (product_left_mono hM hw
    (product_comm hM hw hm) (product_comm hM hw ht) hr)

/-- A strict upper endpoint cannot have an empty numerator, including in
externally nonstandard omega. -/
theorem positive_numerator (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r a b : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hr : Coordinates w r a b) (hqr : Lt hM w q r) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z a := by
  classical
  have h := hqr.1
  obtain ⟨c,d,a',b',hq,hr',u,v,hu,hv,_⟩ := h
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  have huv := (lt_iff_products hM hw hq hr hu hv).mp hqr
  by_cases hn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z a
  · exact hn
  · have hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z a := fun z h => hn ⟨z,h⟩
    have hZF := ModelTransfer.project_models_iff.mp hM
    have hv0 := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
      (hw.members_areOrdinals hZF d hq.2.1) hz).mp (mul_comm hM hw hr.1 hq.2.1 hv)
    exact (hv0 u huv).elim

/-- A nonempty numerator is strictly above the actual zero fraction. -/
theorem zero_lt (hM : FirstOrder.Theory.Models M nativeZF)
    {w q z a b zero one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Coordinates w q a b)
    (hz : Coordinates w z zero one) (hzero : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (han : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) : Lt hM w z q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have h0 := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF b hq.2.1) hzero).mpr hzero
  have hza : (Project.FirstOrderSemantics.reduct M).mem zero a := by
    rcases nat_compare hM hw hz.1 hq.1 with he | hza | haz
    · obtain ⟨p,hp⟩ := han
      exact (hzero p (he.symm ▸ hp)).elim
    · exact hza
    · exact (hzero a haz).elim
  exact (lt_iff_products hM hw hz hq (mul_comm hM hw hq.2.1 hz.1 h0)
    (mul_one hM hw hq.1 hz.2.1 hone).1).mpr hza

def product {m : Nat} (w q r s : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (coordinates w.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ 5 4)
      (.conj (coordinates w.succ.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ.succ 3 2)
        (.conj (coordinates w.succ.succ.succ.succ.succ.succ s.succ.succ.succ.succ.succ.succ 1 0)
          (.conj (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound 1) (.bound 5) (.bound 3))
            (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound 0) (.bound 4) (.bound 2)))))))))))

theorem product_freeClosed {m : Nat} (w q r s : Fin m) : (product w q r s).FreeClosed := by
  simp -implicitDefEqProofs [product,Definitional.Formula.FreeClosed,coordinates_freeClosed]

theorem product_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q r s : Fin m) :
    Project.Formula.satisfies env (product w q r s) ↔
      Product hM (env.bound w) (env.bound q) (env.bound r) (env.bound s) := by
  simp only [product,Product,ConstructionFractionOrder.Mul,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinates_semantics hM,Project.Formula.satisfies_isOrdinalMultiplication_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

end PPAC.Migration.ConstructionFractionProduct
