/- Adapt the accepted source Base.margin / principal cut arithmetic to the
probe's additive PointBound input. Reuse cut_gap and cost antitonicity; do not
reprove the Base margin. Consumer: ProbeMargins inside/outside cost estimates. -/
import PPAC.Migration.ConstructionProbeCostBoundsSyntax
import PPAC.Migration.ConstructionBaseHeightGap

namespace PPAC.Migration.ConstructionBasePointBound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionCutAddition (SumMember AddBound)
open ConstructionBaseWeights (Digits)
open ConstructionBaseMonoid (AdditionGraph Divides)
open ConstructionProbeCostBounds (PointBound)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Nonnegativity of the second fraction, using native natural arithmetic. -/
theorem sum_left_le (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hs : Sum hM w q r s) : Le hM w q s := by
  obtain ⟨a,b,c,d,n,den,hq,hr,hs,ad,cb,had,hcb,hadd,hden⟩ := hs
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have hadw := mul_range hM hw hq.1 hr.2.1 had
  have hcbw := mul_range hM hw hr.1 hq.2.1 hcb
  have hle : NatLe ad n := ZF.ordinalAddition_left_eq_or_mem hZF (KuratowskiZF.interpretation hM) (ord cb hcbw) hadd
  obtain ⟨adb,_,hadb⟩ := mul_exists hM hw hadw hq.2.1
  obtain ⟨nb,_,hnb⟩ := mul_exists hM hw hs.1 hq.2.1
  obtain ⟨aden,_,haden⟩ := mul_exists hM hw hq.1 hs.2.1
  have he := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a hq.1) (ord d hr.2.1) (ord b hq.2.1) had (mul_comm hM hw hq.2.1 hr.2.1 hden) haden hadb
  have hmult := (mul_le_iff hM hw hq.2.1 hq.2.2.1 hadw hs.1
    (mul_comm hM hw hadw hq.2.1 hadb) (mul_comm hM hw hs.1 hq.2.1 hnb)).mpr hle
  exact (le_iff_products hM hw hq hs haden hnb).mpr (he.symm ▸ hmult)

theorem sum_right_le (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hs : Sum hM w q r s) : Le hM w r s :=
  sum_left_le hM hw (ConstructionFractionAddition.sum_comm hM hw hs)

/-- Every represented principal sum satisfies the new general additive bound.
Only this implication is needed; equality of all addition implementations is not assumed. -/
theorem principal_add_bound (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hadd : ConstructionPrincipalAddition.PrincipalAdd hM w Q a b c) : AddBound hM w a b c := by
  obtain ⟨q,r,s,hq,hr,ha,hb,hs,hc⟩ := hadd
  intro p hp
  rcases hp with hp | hp | ⟨u,v,z,hu,hv,hz,hpz⟩
  · obtain ⟨hpQ,hpq⟩ := (ha p).mp hp
    exact (hc p).mpr ⟨hpQ,lt_le_trans hM hw hpq (sum_left_le hM hw hs)⟩
  · obtain ⟨hpQ,hpr⟩ := (hb p).mp hp
    exact (hc p).mpr ⟨hpQ,lt_le_trans hM hw hpr (sum_right_le hM hw hs)⟩
  · obtain ⟨huQ,huq⟩ := (ha u).mp hu
    obtain ⟨hvQ,hvr⟩ := (hb v).mp hv
    obtain ⟨mid,hm⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ q).mp hq) ((hQ v).mp hvQ)
    have hzm := (ConstructionFractionAddition.sum_right_lt_iff hM hw hz hm).mpr huq
    have hms := (ConstructionFractionAddition.sum_left_le_iff hM hw hm hs).mpr hvr.1
    have hpzCopy := hpz
    obtain ⟨i,j,k,l,hp,_,_⟩ := hpzCopy
    exact (hc p).mpr ⟨(hQ p).mpr ⟨i,j,hp⟩,le_lt_trans hM hw hpz (lt_le_trans hM hw hzm hms)⟩

theorem bound_inputs_mono {hM : FirstOrder.Theory.Models M nativeZF} {w a b a' b' c : M.Carrier .set}
    (h : AddBound hM w a b c) (ha : Subset a' a) (hb : Subset b' b) : AddBound hM w a' b' c := by
  intro p hp
  rcases hp with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
  · exact h p (Or.inl (ha p hp))
  · exact h p (Or.inr (Or.inl (hb p hp)))
  · exact h p (Or.inr (Or.inr ⟨q,r,s,ha q hq,hb r hr,hs,hps⟩))

theorem cost_value_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q C x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q C)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w) : ∃ c, PureKuratowski.PairMember M x c C := by
  obtain ⟨q,hq⟩ := ConstructionBaseWeights.weight_exists hM false hw hd.1 hd.2.1
    ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hd.2.2.1 hx
  obtain ⟨c,hcP⟩ := exists_principal hM w Q q
  exact ⟨c,(hc x c).mpr ⟨hx,q,hq,hcP⟩⟩

/-- The exact old PointBound used by the probe, on actual source Base graphs. -/
theorem base_point_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q mul H C : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hg : AdditionGraph hM w mul)
    (hh : ConstructionCutWeights.Graph hM true w one two one Q H)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q C) : PointBound hM w w mul H C := by
  intro x y d hx hy cd hxh hyh hdc hxy hdy hdx
  have hxw := ((hh x hx).mp hxh).1
  have hyw := ((hh y hy).mp hyh).1
  have hdw := ((hc d cd).mp hdc).1
  have hdxNat : ¬ NatLe d x := fun h => hdx ((ConstructionBaseMonoid.le_iff hM hw hg hdw hxw).mpr h)
  have hxyStrict : (Project.FirstOrderSemantics.reduct M).mem x y := by
    rcases (ConstructionBaseMonoid.le_iff hM hw hg hxw hyw).mp hxy with he | hxy
    · subst y
      exact (hdx hdy).elim
    · exact hxy
  obtain ⟨cx,hxc⟩ := cost_value_exists hM hw hd hc hxw
  obtain ⟨gap,_,hadd,hcg,_⟩ := ConstructionBaseHeightGap.cut_gap hM hw hd hQ hxw hyw hxyStrict
    ((hh x hx).mp hxh).2 ((hh y hy).mp hyh).2 ((hc x cx).mp hxc).2
  have hdcx := ConstructionBaseCostBound.missing_cost_bound hM hw hd hQ hc hxc hdc hdxNat
  exact bound_inputs_mono (principal_add_bound hM hw hQ hadd) (fun _ h => h) (fun p hp => hcg p (hdcx p hp))

/-- Reuse the existing numeric constructor, retaining the full previously proved
strict Base margin on the very same graphs alongside the new PointBound. -/
theorem exists_base (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul one two three Q R H C unitCode unit,
      AdditionGraph hM w mul ∧ Digits w one two three ∧ Carrier w Q ∧ CutCarrier hM w Q R ∧
      ConstructionCutWeights.Graph hM true w one two one Q H ∧
      ConstructionCutWeights.Graph hM false w one two three Q C ∧
      ConstructionCutWeights.RangeCuts R H ∧ ConstructionCutWeights.RangeCuts R C ∧
      Coordinates w unitCode one one ∧ Principal hM w Q unitCode unit ∧
      (Project.FirstOrderSemantics.reduct M).mem unit R ∧
      ConstructionCutWeights.RangeBound unit H ∧ ConstructionCutWeights.RangeBound unit C ∧
      (∀ x y qx qy cx, PureKuratowski.PairMember M x qx H → PureKuratowski.PairMember M y qy H →
        PureKuratowski.PairMember M x cx C → (Project.FirstOrderSemantics.reduct M).mem x y →
        ConstructionBaseHeightGap.MarginAt hM w Q C x y qx qy) ∧ PointBound hM w w mul H C := by
  obtain ⟨mul,hg⟩ := ConstructionBaseMonoid.exists_additionGraph hM hw
  obtain ⟨one,two,three,Q,R,H,C,unitCode,unit,hd,hQ,hR,hh,hc,hhr,hcr,hu,hunit,hur,hhb,hcb⟩ :=
    ConstructionCutWeights.exists_bounded_weights hM hw
  exact ⟨mul,one,two,three,Q,R,H,C,unitCode,unit,hg,hd,hQ,hR,hh,hc,hhr,hcr,hu,hunit,hur,hhb,hcb,
    fun _ _ _ _ _ hxh hyh hxc hxy => ConstructionBaseHeightGap.source_margin hM hw hd hQ hh hc hxh hyh hxc hxy,
    base_point_bound hM hw hd hQ hg hh hc⟩

end PPAC.Migration.ConstructionBasePointBound
