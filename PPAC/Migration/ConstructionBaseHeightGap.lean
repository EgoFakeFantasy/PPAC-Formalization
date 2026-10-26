/- Pinned Base.margin strict estimate. Native successor/exponent arithmetic
provides the exact two successive denominator doublings. The final native
certificate constructs the actual bounded weight graphs with their full strict
cut margin; it does not assert arbitrary-cut field operations or the final monoid. -/
import PPAC.Migration.ConstructionBaseCostBound
import PPAC.Migration.ConstructionFractionDifference

namespace PPAC.Migration.ConstructionBaseHeightGap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBaseWeights ConstructionFractionOrder ConstructionFractionDensity
open ConstructionFractionAddition ConstructionFractionDifference ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Native finite successor is addition by the internal one. -/
theorem succ_add (hM : FirstOrder.Theory.Models M nativeZF) {one a b : M.Carrier .set}
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf b a) : Add hM a one b :=
  (ZF.ordinalAddition_one_iff (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hone).mpr hs

theorem same_den_le (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a d) (hr : Coordinates w r b d) : Le hM w q r ↔ NatLe a b := by
  obtain ⟨ad,_,had⟩ := mul_exists hM hw hq.1 hq.2.1
  obtain ⟨bd,_,hbd⟩ := mul_exists hM hw hr.1 hr.2.1
  exact (le_iff_products hM hw hq hr had hbd).trans
    (mul_le_iff hM hw hq.2.1 hq.2.2.1 hq.1 hr.1
      (mul_comm hM hw hq.1 hq.2.1 had) (mul_comm hM hw hr.1 hr.2.1 hbd))

theorem same_den_strict (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a d) (hr : Coordinates w r b d)
    (hab : (Project.FirstOrderSemantics.reduct M).mem a b) : Lt hM w q r :=
  ⟨(same_den_le hM hw hq hr).mpr (Or.inr hab),fun h =>
    nat_not_reverse hM hw hq.1 ((same_den_le hM hw hr hq).mp h) hab⟩

/-- (p-1)/p is monotone in its positive internal denominator. -/
theorem complement_mono (hM : FirstOrder.Theory.Models M nativeZF) {w one q r a b p t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hq : Coordinates w q a p) (hr : Coordinates w r b t)
    (hp : (Project.FirstOrderSemantics.reduct M).SuccessorOf p a)
    (ht : (Project.FirstOrderSemantics.reduct M).SuccessorOf t b) (hpt : NatLe p t) : Le hM w q r := by
  have ha := succ_add hM hone hp
  have hb := succ_add hM hone ht
  have hab : NatLe a b := (add_le_iff hM hw ho hq.1 hr.1
    (add_comm hM hw hq.1 ho ha) (add_comm hM hw hr.1 ho hb)).mp hpt
  obtain ⟨ab,hAb,habm⟩ := mul_exists hM hw hq.1 hr.1
  obtain ⟨aprod,_,hat⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨bp,_,hbp⟩ := mul_exists hM hw hr.1 hq.2.1
  have hAt := mul_add hM hw hq.1 hr.1 ho hb hat habm (mul_one hM hw hq.1 ho hone).1
  have hBp := mul_add hM hw hr.1 hq.1 ho ha hbp (mul_comm hM hw hq.1 hr.1 habm) (mul_one hM hw hr.1 ho hone).1
  exact (le_iff_products hM hw hq hr hat hbp).mpr ((add_le_iff hM hw hAb hq.1 hr.1 hAt hBp).mpr hab)

theorem height_coordinates (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two n q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z two)
    (hq : Weight hM true w one two one n q) :
    ∃ a p, Denominator hM w two one n p ∧ Coordinates w q a p ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf p a := by
  obtain ⟨p,hp,a,ha,hpa,hq⟩ := hq
  exact ⟨a,p,hp,⟨ha,hp.choose_spec.2.1,denominator_nonempty hM hw ht htn hp,hq⟩,hpa⟩

theorem height_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three n m q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w) (hnm : NatLe n m)
    (hq : Weight hM true w one two one n q) (hr : Weight hM true w one two one m r) : Le hM w q r := by
  obtain ⟨a,p,hp,hq,hpa⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hq
  obtain ⟨b,t,ht,hr,htb⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hr
  exact complement_mono hM hw hd.1 hd.2.2.2.1 hq hr hpa htb
    (ConstructionBaseCostBound.denominator_mono hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.1 hn hm hnm hp ht)

/-- The source pow_succ relation, with both internal sum witnesses identified. -/
theorem denominator_successor (hM : FirstOrder.Theory.Models M nativeZF)
    {w two offset next n p t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hnext : (Project.FirstOrderSemantics.reduct M).SuccessorOf next offset)
    (hp : Denominator hM w two offset n p) (htp : Denominator hM w two next n t) : Mul hM p two t := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨k,hk,_,hnk,hp⟩ := hp
  obtain ⟨l,_,_,hnl,htp⟩ := htp
  obtain ⟨k',hk',hkl⟩ := (ZF.ordinalAddition_successor_iff hZF I (ord offset ho) hnext).mp hnl
  have ek := ConstructionBaseMonoid.addition_unique hM hw ho hk' hnk
  subst k'
  obtain ⟨p',hp',hpt⟩ := (ZF.ordinalExponentiation_successor_iff hZF I (ord two ht) (ord k hk) hkl).mp htp
  obtain ⟨v,_,hv⟩ := ZF.ordinalExponentiation_existsUnique hZF I (ord two ht) (ord k hk)
  have ep := (hv p' hp').trans (hv p hp).symm
  exact ep ▸ hpt

/-- (n+1)+1=n+2 aligns the next actual height with the source intermediate power. -/
theorem next_denominator (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three n next p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf next n)
    (hp : Denominator hM w two one next p) : Denominator hM w two two n p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨k,hk,hpω,hkadd,hpow⟩ := hp
  obtain ⟨l,_,hl⟩ := add_exists hM hw hn hd.2.1
  have he := ZF.ordinalAddition_assoc hZF I (ord n hn) (ord one hd.1) (ord one hd.1)
    (succ_add hM hd.2.2.2.1 hs) (succ_add hM hd.2.2.2.1 hd.2.2.2.2.1) hl hkadd
  exact ⟨k,hk,hpω,he ▸ hl,hpow⟩

/-- Doubling a successor gives two successors beyond the doubled predecessor. -/
theorem double_successor (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three a p aa pp : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w)
    (hpa : (Project.FirstOrderSemantics.reduct M).SuccessorOf p a)
    (haa : Mul hM a two aa) (hpp : Mul hM p two pp) : Add hM aa two pp := by
  have hpw := ZF.ordinalAddition_mem_omega (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hw ha hd.1 (succ_add hM hd.2.2.2.1 hpa)
  exact mul_add hM hw hd.2.1 ha hd.1 (succ_add hM hd.2.2.2.1 hpa)
    (mul_comm hM hw hpw hd.2.1 hpp) (mul_comm hM hw ha hd.2.1 haa) (mul_one hM hw hd.2.1 hd.1 hd.2.2.2.1).1

/-- Source adjacent-step estimate, using exactly the two doubled denominators. -/
theorem adjacent_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three q r cost a b p p2 p4 : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hq : Coordinates w q a p) (hr : Coordinates w r b p2) (hc : Coordinates w cost one p4)
    (hpa : (Project.FirstOrderSemantics.reduct M).SuccessorOf p a)
    (hpb : (Project.FirstOrderSemantics.reduct M).SuccessorOf p2 b)
    (hp2 : Mul hM p two p2) (hp4 : Mul hM p2 two p4) :
    ∃ s, Sum hM w q cost s ∧ Lt hM w s r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨aa,hAa,haa⟩ := mul_exists hM hw hq.1 hd.2.1
  obtain ⟨aaaa,hAaaa,haaaa⟩ := mul_exists hM hw hAa hd.2.1
  obtain ⟨bb,hBb,hbb⟩ := mul_exists hM hw hr.1 hd.2.1
  obtain ⟨v,hva,hp2v⟩ := (ZF.ordinalAddition_two_iff hZF I ⟨one,hd.2.2.2.1,hd.2.2.2.2.1⟩).mp
    (double_successor hM hw hd hq.1 hpa haa hp2)
  have eb : b = v := Structure.SuccessorOf.predecessor_eq (ModelTransfer.extensionality hM) (ord b hr.1) hpb hp2v
  have hba : (Project.FirstOrderSemantics.reduct M).SuccessorOf b aa := eb.symm ▸ hva
  obtain ⟨c,hca,hbbc⟩ := (ZF.ordinalAddition_two_iff hZF I ⟨one,hd.2.2.2.1,hd.2.2.2.2.1⟩).mp
    (double_successor hM hw hd hAa hba haaaa hbb)
  have hC := add_range hM hw hAaaa hd.1 (succ_add hM hd.2.2.2.1 hca)
  obtain ⟨q2,hq2c⟩ := KuratowskiZF.exists_code hM aa p2
  obtain ⟨q4,hq4c⟩ := KuratowskiZF.exists_code hM aaaa p4
  obtain ⟨r2,hr2c⟩ := KuratowskiZF.exists_code hM bb p4
  obtain ⟨t,htc⟩ := KuratowskiZF.exists_code hM c p4
  have hq2 : Coordinates w q2 aa p2 := ⟨hAa,hr.2.1,hr.2.2.1,hq2c⟩
  have hq4 : Coordinates w q4 aaaa p4 := ⟨hAaaa,hc.2.1,hc.2.2.1,hq4c⟩
  have hr2 : Coordinates w r2 bb p4 := ⟨hBb,hc.2.1,hc.2.2.1,hr2c⟩
  have ht : Coordinates w t c p4 := ⟨hC,hc.2.1,hc.2.2.1,htc⟩
  have e12 := scaled_equiv hM hw hq hq2 hd.2.1 haa hp2
  have e24 := scaled_equiv hM hw hq2 hq4 hd.2.1 haaaa hp4
  have er := scaled_equiv hM hw hr hr2 hd.2.1 hbb hp4
  obtain ⟨s,hs⟩ := sum_exists hM hw ⟨a,p,hq⟩ ⟨one,p4,hc⟩
  obtain ⟨s',hs'⟩ := sum_exists hM hw ⟨aaaa,p4,hq4⟩ ⟨one,p4,hc⟩
  have eqsum := sum_equiv hM hw hs hs'
    ⟨le_trans hM hw e12.1 e24.1,le_trans hM hw e24.2 e12.2⟩
    ⟨le_refl hM hw ⟨one,p4,hc⟩,le_refl hM hw ⟨one,p4,hc⟩⟩
  have eqt := same_den_sum hM hw hq4 hc ht (succ_add hM hd.2.2.2.1 hca) hs'
  exact ⟨s,hs,lt_le_trans hM hw
    (le_lt_trans hM hw (le_trans hM hw eqsum.1 eqt.1) (same_den_strict hM hw ht hr2 hbbc.predecessor_mem)) er.2⟩

/-- The source strict estimate for every pair of internal indices x<y. -/
theorem weight_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three x y q r cost : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hxy : (Project.FirstOrderSemantics.reduct M).mem x y)
    (hq : Weight hM true w one two one x q) (hr : Weight hM true w one two one y r)
    (hc : Weight hM false w one two three x cost) : ∃ s, Sum hM w q cost s ∧ Lt hM w s r := by
  obtain ⟨next,hnx,hnw⟩ := hw.1.2 x hx
  obtain ⟨mid,hmid⟩ := weight_exists hM true hw hd.1 hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hd.1 hnw
  obtain ⟨a,p,hp,hqc,hpa⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hq
  obtain ⟨b,p2,hp2,hmc,hpb⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hmid
  obtain ⟨p4,hp4,hcc⟩ := ConstructionBaseCostBound.cost_coordinates hM hw hd hc
  have hp2' := next_denominator hM hw hd hx hnx hp2
  have hmul2 := denominator_successor hM hw hd.2.1 hd.1 hd.2.2.2.2.1 hp hp2'
  have hmul4 := denominator_successor hM hw hd.2.1 hd.2.1 hd.2.2.2.2.2 hp2' hp4
  obtain ⟨s,hs,hsm⟩ := adjacent_gap hM hw hd hqc hmc hcc hpa hpb hmul2 hmul4
  have hny : NatLe next y := by
    rcases nat_compare hM hw hnw hy with he | hny | hyn
    · exact Or.inl he
    · exact Or.inr hny
    · rcases (hnx y).mp hyn with hyx | heq
      · exact (nat_not_reverse hM hw hx (Or.inr hyx) hxy).elim
      · have he := (ModelTransfer.extensionality hM).eq_of_same_members y x heq
        exact (nat_not_reverse hM hw hx (Or.inl he) hxy).elim
  exact ⟨s,hs,lt_le_trans hM hw hsm (height_mono hM hw hd hnw hy hny hmid hr)⟩

/-- Strict comparison with the actual, uniquely determined principal difference. -/
theorem cut_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q x y qx qy cx : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hx : (Project.FirstOrderSemantics.reduct M).mem x w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hxy : (Project.FirstOrderSemantics.reduct M).mem x y)
    (hqx : ConstructionCutWeights.Value hM true w one two one Q x qx)
    (hqy : ConstructionCutWeights.Value hM true w one two one Q y qy)
    (hcx : ConstructionCutWeights.Value hM false w one two three Q x cx) :
    ∃ gap, ConstructionPrincipalAddition.Represented hM w Q gap ∧
      ConstructionPrincipalAddition.PrincipalAdd hM w Q qx gap qy ∧ Subset cx gap ∧ ¬ Subset gap cx := by
  obtain ⟨q,hq,hqc⟩ := hqx
  obtain ⟨r,hr,hrc⟩ := hqy
  obtain ⟨c,hc,hcc⟩ := hcx
  obtain ⟨a,p,_,hqa,_⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hq
  obtain ⟨b,t,_,hrb,_⟩ := height_coordinates hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hr
  obtain ⟨den,_,hcd⟩ := ConstructionBaseCostBound.cost_coordinates hM hw hd hc
  have hqQ := (hQ q).mpr ⟨a,p,hqa⟩
  have hrQ := (hQ r).mpr ⟨b,t,hrb⟩
  have hcQ := (hQ c).mpr ⟨one,den,hcd⟩
  obtain ⟨v,hv,hvr⟩ := weight_gap hM hw hd hx hy hxy hq hr hc
  obtain ⟨sum,hSum⟩ := exists_principal hM w Q v
  have hvCopy := hv
  obtain ⟨a',b',c',d',nv,dv,_,_,hvCoord,_⟩ := hvCopy
  have hvQ := (hQ v).mpr ⟨nv,dv,hvCoord⟩
  have hsumAdd : ConstructionPrincipalAddition.PrincipalAdd hM w Q qx cx sum :=
    ⟨q,c,v,hqQ,hcQ,hqc,hcc,hv,hSum⟩
  have hsr : Subset sum qy := (principal_subset_iff hM hw hQ hvQ hrQ hSum hrc).mpr hvr.1
  have hnrs : ¬ Subset qy sum := fun h => hvr.2 ((principal_subset_iff hM hw hQ hrQ hvQ hrc hSum).mp h)
  have hqr : Subset qx qy := (principal_subset_iff hM hw hQ hqQ hrQ hqc hrc).mpr
    (height_mono hM hw hd hx hy (Or.inr hxy) hq hr)
  obtain ⟨gap,hgap,hadd⟩ := principal_difference_exists hM hw hQ ⟨q,hqQ,hqc⟩ ⟨r,hrQ,hrc⟩ hqr
  have hcSum := ConstructionPrincipalAddition.add_comm hM hw hsumAdd
  have hgSum := ConstructionPrincipalAddition.add_comm hM hw hadd
  exact ⟨gap,hgap,hadd,(ConstructionPrincipalAddition.add_le_iff hM hw hQ hcSum hgSum).mp hsr,
    fun h => hnrs ((ConstructionPrincipalAddition.add_le_iff hM hw hQ hgSum hcSum).mpr h)⟩

def MarginAt (hM : FirstOrder.Theory.Models M nativeZF) (w Q cost x y qx qy : M.Carrier .set) : Prop :=
  ∃ gap family s, ConstructionPrincipalAddition.Represented hM w Q gap ∧
    ConstructionPrincipalAddition.PrincipalAdd hM w Q qx gap qy ∧
    ConstructionBaseCostBound.MissingFamily cost x y family ∧
    (∃ c, (Project.FirstOrderSemantics.reduct M).mem c family) ∧ Cut hM w Q s ∧
    UpperBound family s ∧ (∀ t, UpperBound family t → Subset s t) ∧ Subset s gap ∧ ¬ Subset gap s

/-- Both source UniformMargin branches, with the exact nonempty image supremum. -/
theorem source_margin (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q height cost x y qx qy cx : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q)
    (hh : ConstructionCutWeights.Graph hM true w one two one Q height)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hqx : PureKuratowski.PairMember M x qx height) (hqy : PureKuratowski.PairMember M y qy height)
    (hcx : PureKuratowski.PairMember M x cx cost)
    (hxy : (Project.FirstOrderSemantics.reduct M).mem x y) : MarginAt hM w Q cost x y qx qy := by
  obtain ⟨hx,hqxv⟩ := (hh x qx).mp hqx
  obtain ⟨hy,hqyv⟩ := (hh y qy).mp hqy
  have hcxv := ((hc x cx).mp hcx).2
  obtain ⟨gap,hg,hadd,hcg,hngc⟩ := cut_gap hM hw hd hQ hx hy hxy hqxv hqyv hcxv
  obtain ⟨family,s,hf,hne,hs,hu,hl,hsc⟩ := ConstructionBaseCostBound.missing_supremum_bound hM hw hd hQ hc hcx hy hxy
  exact ⟨gap,family,s,hg,hadd,hf,hne,hs,hu,hl,fun p hp => hcg p (hsc p hp),
    fun h => hngc (fun p hp => hsc p (h p hp))⟩

def marginAt {m : Nat} (w Q cost x y qx qy : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE
    (.conj (ConstructionPrincipalAddition.represented w.succ.succ.succ Q.succ.succ.succ 2)
      (.conj (ConstructionPrincipalAddition.principalAdd w.succ.succ.succ Q.succ.succ.succ qx.succ.succ.succ 2 qy.succ.succ.succ)
        (.conj (ConstructionBaseCostBound.missingFamily cost.succ.succ.succ x.succ.succ.succ y.succ.succ.succ 1)
          (.conj (.existsE (.mem (.bound 0) (.bound 2)))
            (.conj (cut w.succ.succ.succ Q.succ.succ.succ 0)
              (.conj (supremum (1 : Fin (m+3)) 0)
                (.conj (Project.Formula.subset (.bound 0) (.bound 2))
                  (.neg (Project.Formula.subset (.bound 2) (.bound 0))))))))))))

theorem marginAt_freeClosed {m : Nat} (w Q cost x y qx qy : Fin m) : (marginAt w Q cost x y qx qy).FreeClosed := by
  simp -implicitDefEqProofs [marginAt,Definitional.Formula.FreeClosed,
    ConstructionPrincipalAddition.represented_freeClosed,ConstructionPrincipalAddition.principalAdd_freeClosed,
    ConstructionBaseCostBound.missingFamily_freeClosed,cut_freeClosed,supremum_freeClosed]

theorem marginAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q cost x y qx qy : Fin m) :
    Project.Formula.satisfies env (marginAt w Q cost x y qx qy) ↔
      MarginAt hM (env.bound w) (env.bound Q) (env.bound cost) (env.bound x) (env.bound y) (env.bound qx) (env.bound qy) := by
  simp only [marginAt,MarginAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionPrincipalAddition.represented_semantics hM,ConstructionPrincipalAddition.principalAdd_semantics hM,
    ConstructionBaseCostBound.missingFamily_semantics hM,cut_semantics hM,supremum_semantics,
    Project.Formula.satisfies_subset_iff]
  constructor
  · rintro ⟨g,f,s,hg,ha,hf,hn,hc,⟨hu,hl⟩,hb,hnb⟩
    exact ⟨g,f,s,hg,ha,hf,hn,hc,hu,hl,hb,hnb⟩
  · rintro ⟨g,f,s,hg,ha,hf,hn,hc,hu,hl,hb,hnb⟩
    exact ⟨g,f,s,hg,ha,hf,hn,hc,⟨hu,hl⟩,hb,hnb⟩

def marginLaw {m : Nat} (w Q height cost : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge height.succ.succ.succ.succ.succ 4 2))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge height.succ.succ.succ.succ.succ 3 1))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge cost.succ.succ.succ.succ.succ 4 0))
          (.imp (.mem (.bound 4) (.bound 3))
            (marginAt w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ cost.succ.succ.succ.succ.succ 4 3 2 1)))))))))

theorem marginLaw_freeClosed {m : Nat} (w Q height cost : Fin m) : (marginLaw w Q height cost).FreeClosed := by
  simp -implicitDefEqProofs [marginLaw,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,marginAt_freeClosed]

theorem marginLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q height cost : Fin m) :
    Project.Formula.satisfies env (marginLaw w Q height cost) ↔ ∀ x y qx qy cx,
      PureKuratowski.PairMember M x qx (env.bound height) → PureKuratowski.PairMember M y qy (env.bound height) →
      PureKuratowski.PairMember M x cx (env.bound cost) → (Project.FirstOrderSemantics.reduct M).mem x y →
      MarginAt hM (env.bound w) (env.bound Q) (env.bound cost) x y qx qy := by
  simp only [marginLaw,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,marginAt_semantics hM]
  rfl

/-- Actual source numeric data exist with the full strict margin, not an assumed field. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBaseWeights.digits (9 : Fin 10) 8 7 6)
        (.conj (ConstructionFractionOrder.carrier (9 : Fin 10) 5)
        (.conj (cutCarrier (9 : Fin 10) 5 4)
        (.conj (ConstructionCutWeights.graph true (9 : Fin 10) 8 7 8 5 3)
        (.conj (ConstructionCutWeights.graph false (9 : Fin 10) 8 7 6 5 2)
        (.conj (ConstructionCutWeights.rangeCuts (4 : Fin 10) 3)
        (.conj (ConstructionCutWeights.rangeCuts (4 : Fin 10) 2)
        (.conj (ConstructionFractionOrder.coordinates (9 : Fin 10) 1 8 8)
        (.conj (principal (9 : Fin 10) 5 1 0)
        (.conj (.mem (.bound 0) (.bound 4))
        (.conj (ConstructionCutWeights.rangeBound (0 : Fin 10) 3)
        (.conj (ConstructionCutWeights.rangeBound (0 : Fin 10) 2) (marginLaw (9 : Fin 10) 5 3 2)))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBaseWeights.digits_freeClosed,
    ConstructionFractionOrder.carrier_freeClosed,cutCarrier_freeClosed,ConstructionCutWeights.graph_freeClosed,ConstructionCutWeights.rangeCuts_freeClosed,
    ConstructionFractionOrder.coordinates_freeClosed,principal_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,marginLaw_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionBaseWeights.digits_semantics,ConstructionFractionOrder.carrier_semantics hM,
    cutCarrier_semantics hM,ConstructionCutWeights.graph_semantics hM,ConstructionCutWeights.rangeCuts_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    principal_semantics hM,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCutWeights.rangeBound_semantics hM,marginLaw_semantics hM]
  obtain ⟨one,two,three,Q,R,height,cost,unitCode,unit,hd,hQ,hR,hh,hc,hhr,hcr,hu,hunit,hur,hhb,hcb⟩ :=
    ConstructionCutWeights.exists_bounded_weights hM hw
  exact ⟨one,two,three,Q,R,height,cost,unitCode,unit,hd,hQ,hR,hh,hc,hhr,hcr,hu,hunit,hur,hhb,hcb,
    fun _ _ _ _ _ hqx hqy hcx hxy => source_margin hM hw hd hQ hh hc hqx hqy hcx hxy⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)


end PPAC.Migration.ConstructionBaseHeightGap
