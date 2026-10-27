/- Pinned MergerCones.copiesHeight_lt_one:211, specifically the source
sum_const/n=1 identification. Reuse native constant functions, Raw induction,
principal_sum, natural successor addition and positive-natural scaling.
All internal/nonstandard n; no new finite-sum, sequence or recursion backend. -/
import PPAC.Migration.ConstructionMergerHeightComparison
import PPAC.Migration.ConstructionPrincipalSumBridge

namespace PPAC.Migration.ConstructionMergerHeightUpper
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier Principal)
open ConstructionFractionOrder (Coordinates Carrier)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeHomEvaluation (Eval)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerFiniteWeights (CoordinateEval HeightValue)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem natural_zero_principal (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q zero one p : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : Carrier w Q) (hz : ∀ t, ¬ (Project.FirstOrderSemantics.reduct M).mem t zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hp : Coordinates w p zero one) : Principal hM w Q p zero := by
  intro t
  constructor
  · exact fun ht => (hz t ht).elim
  · rintro ⟨htQ,htp⟩
    exact (htp.2 (ConstructionFractionDifference.zero_le hM hw ((hQ t).mp htQ) hp hz hone)).elim

theorem natural_successor_sum (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q one u top n m p r N K : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : Carrier w Q) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hUnit : Principal hM w Q u top)
    (hp : Coordinates w p n one) (hr : Coordinates w r m one)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n)
    (hN : Principal hM w Q p N) (hK : Principal hM w Q r K) : ConstructionCutAddition.SumCut hM w Q N top K := by
  obtain ⟨s,hSum⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨n,one,hp⟩ ⟨one,one,hu⟩
  have heq := ConstructionFractionDifference.same_den_sum hM hw hp hu hr
    (ConstructionBaseHeightGap.succ_add hM hone hs) hSum
  obtain ⟨S,hS⟩ := ConstructionRealCuts.exists_principal hM w Q s
  have hsQ := (hQ s).mpr (ConstructionCutAssociativity.sum_fraction hSum)
  have hrQ := (hQ r).mpr ⟨m,one,hr⟩
  have hSK := (ConstructionRealCuts.principal_eq_iff hM hw hQ hsQ hrQ hS hK).mpr heq
  exact ConstructionPrincipalSumBridge.principal_sum hM hw hQ
    ⟨p,u,s,(hQ p).mpr ⟨n,one,hp⟩,(hQ u).mpr ⟨one,one,hu⟩,hN,hUnit,hSum,hSK ▸ hS⟩

def constantSumAt {m : Nat} (w Q R zero one add Id top q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound w.succ.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 3 4 R.succ.succ.succ.succ.succ)) (.imp
  (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ.succ) (.bound 3) (.bound
  zero.succ.succ.succ.succ.succ)) (.imp (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ add.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ Id.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 2) (.imp (.forallE
  (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 5 1 0)) (Project.Formula.extensionalEq
  (.bound 0) (.bound top.succ.succ.succ.succ.succ.succ.succ))))) (.imp (ConstructionFractionOrder.coordinates
  w.succ.succ.succ.succ.succ 1 4 one.succ.succ.succ.succ.succ) (.imp (ConstructionRealCuts.principal
  w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 1 0) (Project.Formula.extensionalEq (.bound 2) (.bound
  0))))))))))))))

theorem constantSumAt_freeClosed {m : Nat} (w Q R zero one add Id top q : Fin m) :
    (constantSumAt w Q R zero one add Id top q).FreeClosed := by
  simp -implicitDefEqProofs [constantSumAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,Project.Formula.extensionalEq,ConstructionFractionOrder.coordinates_freeClosed,
    ConstructionRealCuts.principal_freeClosed,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem constantSumAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R zero one add Id top q : Fin m) :
    Project.Formula.satisfies env (constantSumAt w Q R zero one add Id top q) ↔
      ∀ n f y p N, (Project.FirstOrderSemantics.reduct M).mem n (env.bound w) → MapsTo n (env.bound R) f →
        PureKuratowski.Code M (env.bound q) f (env.bound zero) →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound add) (env.bound Id) (env.bound Id) (env.bound q) y →
        (∀ i c, PureKuratowski.PairMember M i c f → c = env.bound top) →
        Coordinates (env.bound w) p n (env.bound one) → Principal hM (env.bound w) (env.bound Q) p N → y = N := by
  simp only [constantSumAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeHomEvaluationSyntax.eval_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.principal_semantics hM]
  rfl

theorem constant_eval_natural (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero one u top add Id q n f y p N : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ t, ¬ (Project.FirstOrderSemantics.reduct M).mem t zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hUnit : Principal hM w Q u top)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hf : MapsTo n R f)
    (hq : PureKuratowski.Code M q f zero) (hy : Eval hM w R R R add Id Id q y)
    (hConst : ∀ i c, PureKuratowski.PairMember M i c f → c = top)
    (hp : Coordinates w p n one) (hN : Principal hM w Q p N) : y = N := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have honen : ∃ t, (Project.FirstOrderSemantics.reduct M).mem t one := by
    obtain ⟨z,_,hs⟩ := hone
    exact ⟨z,hs.predecessor_mem⟩
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases zero (Fin.cases one (Fin.cases add (Fin.cases Id (fun _ => top))))))),
    free := fun _ => w }
  let property : Project.UnarySchema 8 := {
    body := constantSumAt 1 2 3 4 5 6 7 8 0,freeClosed := constantSumAt_freeClosed _ _ _ _ _ _ _ _ _ }
  have he (q) : property.denote env q ↔ ∀ n f y p N,
      (Project.FirstOrderSemantics.reduct M).mem n w → MapsTo n R f → PureKuratowski.Code M q f zero →
      Eval hM w R R R add Id Id q y → (∀ i c, PureKuratowski.PairMember M i c f → c = top) →
      Coordinates w p n one → Principal hM w Q p N → y = N :=
    constantSumAt_semantics hM (env.push q) 1 2 3 4 5 6 7 8 0
  have hall := ConstructionProbeEvaluationLaws.raw_induction hM env property hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro n f y p N hn hf hq hy _ hp hN
    have hfx := PureKuratowski.code_injective hOld.2 hq
    have hxzero : x = zero := hfx.2
    have hfzero : f = zero := hfx.1.symm
    have hnzero : n = zero := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (hfzero.symm ▸ SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
    have hpzero : Coordinates w p zero one := by simpa only [hnzero] using hp
    have hNzero := ConstructionRealCuts.principal_unique hM hN (natural_zero_principal hM hw hQ hz hone hpzero)
    have hyzero : y = zero := ((hId x y).mp (ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld hy)).2.symm.trans hxzero
    exact hyzero.trans hNzero.symm) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro n f y p N hn hf hq hy hConst hp hN
    obtain ⟨v,hv,a,hsa,hprod⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons hy
    have hae := ((hId s a).mp hsa).2
    subst a
    obtain ⟨k,m,pref,full,x,hk,hm,hSucc,hpref,hfull,_,_,ht,hcode,happend⟩ := hCons
    have hfx := PureKuratowski.code_injective hcode hq
    have hxzero : x = zero := hfx.2
    have hnEq : n = m := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (hfx.1 ▸ ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hm) hfull)
    have hConstPref : ∀ i c, PureKuratowski.PairMember M i c pref → c = top :=
      fun i c hic => hConst i c (hfx.1 ▸ (happend i c).mpr (Or.inl hic))
    have hsTop := hConst k s (hfx.1 ▸ (happend k s).mpr (Or.inr ⟨rfl,rfl⟩))
    obtain ⟨pk,hpk⟩ := KuratowskiZF.exists_code hM k one
    have hpkCoord : Coordinates w pk k one := ⟨hk,hu.1,honen,hpk⟩
    obtain ⟨K,hK⟩ := ConstructionRealCuts.exists_principal hM w Q pk
    have hvK := (he t).mp ih k pref v pk K hk hpref (hxzero ▸ ht) hv hConstPref hpkCoord hK
    have hpm : Coordinates w p m one := by simpa only [hnEq] using hp
    have hExpected := natural_successor_sum hM hw hQ hu hone hUnit hpkCoord hpm hSucc hK hN
    have hActual : ConstructionCutAddition.SumCut hM w Q K top y := by
      simpa only [hvK,hsTop] using ConstructionCutArithmetic.sum_comm hM hw ((hAdd s v y).mp hprod).2.2
    exact ConstructionCutAddition.sum_unique hM hActual hExpected)
  exact (he q).mp (hall q (ConstructionProbeHomEvaluation.eval_raw hM hy)) n f y p N hn hf hq hy hConst hp hN

/-- The represented internal natural n divided by n is the SAME canonical
unit cut; the equality uses scaling strict-order reflection on all codes. -/
theorem natural_division_unit (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n one u p top N : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : Carrier w Q) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hUnit : Principal hM w Q u top)
    (hp : Coordinates w p n one) (hN : Principal hM w Q p N)
    (hnp : ∃ t, (Project.FirstOrderSemantics.reduct M).mem t n) : ConstructionCutDivision.Value hM w Q n N top := by
  have hTimesUnit : ConstructionFractionScaling.Times hM w n u p :=
    ⟨one,one,n,hu,(ConstructionFractionOrder.mul_one hM hw hp.1 hu.1 hone).2,hp⟩
  intro q
  constructor
  · intro hqt
    obtain ⟨hqQ,hqu⟩ := (hUnit q).mp hqt
    obtain ⟨r,hr⟩ := ConstructionFractionScaling.exists_times hM hw hp.1 ((hQ q).mp hqQ)
    have hrp := (ConstructionFractionScaling.strict_iff hM hw hp.1 hnp hr hTimesUnit).mpr hqu
    exact ⟨hqQ,r,hr,(hN r).mpr ⟨(hQ r).mpr (ConstructionFractionScaling.times_range hr),hrp⟩⟩
  · rintro ⟨hqQ,r,hr,hrN⟩
    exact (hUnit q).mpr ⟨hqQ,(ConstructionFractionScaling.strict_iff hM hw hp.1 hnp hr hTimesUnit).mp ((hN r).mp hrN).2⟩

/-- Literal finite average <1, with the actual constant row constructed
by the donor function constructor and evaluated by the accepted evaluator. -/
theorem average_lt_unit (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero one u top n J add Id CH z a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ t, ¬ (Project.FirstOrderSemantics.reduct M).mem t zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hUnit : Principal hM w Q u top)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ t, (Project.FirstOrderSemantics.reduct M).mem t n)
    (hJ : Representatives R R J) (hAddMap : MapsTo J R add) (hIdMap : MapsTo R R Id)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hBound : ∀ i z c, Product CH i z c → Strict c top)
    (ha : HeightValue hM w Q n R add Id zero CH z a) : Strict a top := by
  obtain ⟨sum,hSum,hDiv⟩ := ha
  obtain ⟨f,q,hf,hRow,hq,hEval⟩ := hSum
  have hTopR := (hR top).mpr (ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hUnit)
  have hZeroR := ConstructionMergerCoordinateLaws.empty_cut_mem hM hR hz hTopR
  obtain ⟨g,hg,hgGraph⟩ := ZF.exists_constantFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (source := n) hTopR
  have hgMap : MapsTo n R g := (ForcingSupportSize.native_mapsTo hM n R g).mpr hg
  have hgEdge (i c) : PureKuratowski.PairMember M i c g ↔ (Project.FirstOrderSemantics.reduct M).mem i n ∧ c = top := hgGraph i c
  obtain ⟨r,hr⟩ := KuratowskiZF.exists_code hM g zero
  obtain ⟨total,hEvalG⟩ := ConstructionProbeHomEvaluation.eval_total hM hw hJ hAddMap hIdMap hIdMap
    ⟨g,zero,⟨n,hn,hgMap⟩,hZeroR,hr⟩
  obtain ⟨p,hpCode⟩ := KuratowskiZF.exists_code hM n one
  have hp : Coordinates w p n one := ⟨hn,hu.1,hu.2.2.1,hpCode⟩
  obtain ⟨N,hN⟩ := ConstructionRealCuts.exists_principal hM w Q p
  have hTotalN := constant_eval_natural hM hw hz hzw hQ hu hone hUnit hId hAdd hn hgMap hr hEvalG
    (fun i c hic => ((hgEdge i c).mp hic).2) hp hN
  have hNatDiv := natural_division_unit hM hw hQ hu hone hUnit hp hN hnp
  have hTotalDiv : ConstructionCutDivision.Value hM w Q n total top := hTotalN.symm ▸ hNatDiv
  have hCompare := ConstructionMergerHeightComparison.sum_eval_comparison hM hw hz hzw hQ hR hId hAdd hn hf hgMap hq hr hEval hEvalG (by
    intro i c d hic hid
    obtain ⟨_,rfl⟩ := (hgEdge i d).mp hid
    exact (hBound i z c ((hRow i c).mp hic).2).1)
  obtain ⟨i,hi⟩ := hnp
  obtain ⟨c,hic,_⟩ := hf.1.2 i hi
  have hStrictSum := hCompare.2 ⟨i,c,top,hic,(hgEdge i top).mpr ⟨hi,rfl⟩,hBound i z c ((hRow i c).mp hic).2⟩
  exact (ConstructionCutDivision.strict_iff hw hQ hn ⟨i,hi⟩
    ((hR sum).mp (ConstructionProbeHomEvaluation.eval_range hM hEval))
    ((hR total).mp (ConstructionProbeHomEvaluation.eval_range hM hEvalG)) hDiv hTotalDiv).mpr hStrictSum

/-- Consume the already constructed coordinate bounds, with top positivity
from the original old height graph. No new coordinate upper-bound oracle. -/
theorem copiesHeight_lt_one (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero one u top n J add Id CH L projection Height Cost CC e unitHeight : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ t, ¬ (Project.FirstOrderSemantics.reduct M).mem t zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hUnit : Principal hM w Q u top)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ t, (Project.FirstOrderSemantics.reduct M).mem t n)
    (hJ : Representatives R R J) (hAddMap : MapsTo J R add) (hIdMap : MapsTo R R Id)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hCH : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hCC : ConstructionMergerCoordinates.Graph n L projection Cost top CC)
    (hEdge : PureKuratowski.PairMember M e unitHeight Height) :
    ∀ z a, HeightValue hM w Q n R add Id zero CH z a → Strict a top := by
  have hTopN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top := by
    obtain ⟨p,hp⟩ := (hHB e unitHeight hEdge).1
    exact ⟨p,(hHB e unitHeight hEdge).2.1 p hp⟩
  have hBounds := (ConstructionMergerCoordinateLaws.coordinate_bounds hz hTopN hHB hCB hCH hCC).1
  exact fun _ _ ha => average_lt_unit hM hw hz hzw hQ hR hu hone hUnit hn hnp hJ hAddMap hIdMap hId hAdd
    (fun i z c hc => (hBounds i z c hc).2) ha

end PPAC.Migration.ConstructionMergerHeightUpper
