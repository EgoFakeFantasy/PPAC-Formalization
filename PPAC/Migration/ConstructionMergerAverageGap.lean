/- Pinned MergerCones.copiesHeight_gap:234 -> copies_coordinate_margin:289.
Reuse accepted fraction distribution, inverse-value scaling, Raw induction,
paired sequence decomposition and cut difference/cancellation. All internal
lengths and the literal coordinate-gap/n <= average-gap expression retained.
No new real field, finite-fold, sequence, recursion or Choice backend. -/
import PPAC.Migration.ConstructionMergerHeightUpper
import PPAC.Migration.ConstructionCutProductArithmetic

namespace PPAC.Migration.ConstructionMergerAverageGap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionFractionOrder (Coordinates Carrier Fraction Le)
open ConstructionFractionDensity (Lt)
open ConstructionCutAddition (SumCut)
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

theorem times_as_product (hM : FirstOrder.Theory.Models M nativeZF)
    {w n one k q r : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hk : Coordinates w k n one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hr : ConstructionFractionScaling.Times hM w n q r) : ConstructionFractionProduct.Product hM w q k r := by
  obtain ⟨a,b,an,hq,hmul,hr⟩ := hr
  exact ⟨a,b,n,one,an,b,hq,hk,hr,hmul,(ConstructionFractionOrder.mul_one hM hw hq.2.1 hk.2.1 hone).1⟩

/-- Positive-natural scaling distributes over the EXISTING fraction sum,
by direct specialization of the already accepted product distribution. -/
theorem times_sum_equiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w n q r s nq nr ns t : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hs : ConstructionFractionAddition.Sum hM w q r s)
    (hq : ConstructionFractionScaling.Times hM w n q nq)
    (hr : ConstructionFractionScaling.Times hM w n r nr)
    (hns : ConstructionFractionScaling.Times hM w n s ns)
    (ht : ConstructionFractionAddition.Sum hM w nq nr t) : Le hM w ns t ∧ Le hM w t ns := by
  obtain ⟨zero,hzero,hzw⟩ := hw.1.1
  obtain ⟨one,hOne,how⟩ := hw.1.2 zero hzw
  have hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one := ⟨zero,hzero,hOne⟩
  obtain ⟨k,hk⟩ := KuratowskiZF.exists_code hM n one
  have hkCoord : Coordinates w k n one := ⟨hn,how,⟨zero,hOne.predecessor_mem⟩,hk⟩
  exact ConstructionFractionProductArithmetic.fraction_distrib hM hw hs
    (ConstructionFractionProduct.product_comm hM hw (times_as_product hM hw hkCoord hone hns))
    (ConstructionFractionProduct.product_comm hM hw (times_as_product hM hw hkCoord hone hq))
    (ConstructionFractionProduct.product_comm hM hw (times_as_product hM hw hkCoord hone hr)) ht

/-- Exact addition preservation for the actual positive-integer division
relation, including zero cuts and all internal nonstandard integers. -/
theorem division_sum (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n a b c da db dc : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : Carrier w Q) (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hs : SumCut hM w Q a b c)
    (hda : ConstructionCutDivision.Value hM w Q n a da)
    (hdb : ConstructionCutDivision.Value hM w Q n b db)
    (hdc : ConstructionCutDivision.Value hM w Q n c dc) : SumCut hM w Q da db dc := by
  have hc := ConstructionCutAssociativity.sum_is_cut hM hw hQ ha hb hs
  intro x
  constructor
  · intro hx
    obtain ⟨hxQ,nx,hxScale,hnxc⟩ := (hdc x).mp hx
    refine ⟨hxQ,?_⟩
    rcases ((hs nx).mp hnxc).2 with hnxA | hnxB | ⟨p,q,s,hpa,hqb,hSum,hNXLe⟩
    · exact Or.inl ((hda x).mpr ⟨hxQ,nx,hxScale,hnxA⟩)
    · exact Or.inr (Or.inl ((hdb x).mpr ⟨hxQ,nx,hxScale,hnxB⟩))
    · obtain ⟨u,nu,hu,hnu,hnup,hpnu⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ p).mp (ha.1 p hpa))
      obtain ⟨v,nv,hv,hnv,hnvq,hqnv⟩ := ConstructionFractionScaling.inverse_value hM hw hn hnp ((hQ q).mp (hb.1 q hqb))
      have huda := (hda u).mpr ⟨(hQ u).mpr hu,nu,hnu,ha.2.1 nu p hpa hnup⟩
      have hvdb := (hdb v).mpr ⟨(hQ v).mpr hv,nv,hnv,hb.2.1 nv q hqb hnvq⟩
      obtain ⟨uv,hUV⟩ := ConstructionFractionAddition.sum_exists hM hw hu hv
      obtain ⟨nuv,hNUV⟩ := ConstructionFractionScaling.exists_times hM hw hn (ConstructionCutAssociativity.sum_fraction hUV)
      obtain ⟨sumN,hSumN⟩ := ConstructionFractionAddition.sum_exists hM hw
        (ConstructionFractionScaling.times_range hnu) (ConstructionFractionScaling.times_range hnv)
      have hScaleEq := times_sum_equiv hM hw hn hUV hnu hnv hNUV hSumN
      have hSumEq := ConstructionFractionAddition.sum_equiv hM hw hSum hSumN ⟨hpnu,hnup⟩ ⟨hqnv,hnvq⟩
      have hXUV := (ConstructionFractionScaling.order_iff hM hw hn hnp hxScale hNUV).mp
        (ConstructionFractionOrder.le_trans hM hw hNXLe (ConstructionFractionOrder.le_trans hM hw hSumEq.1 hScaleEq.2))
      exact Or.inr (Or.inr ⟨u,v,uv,huda,hvdb,hUV,hXUV⟩)
  · rintro ⟨hxQ,hx⟩
    rcases hx with hxA | hxB | ⟨u,v,s,huda,hvdb,hUV,hXUV⟩
    · obtain ⟨_,nx,hxScale,hnxa⟩ := (hda x).mp hxA
      exact (hdc x).mpr ⟨hxQ,nx,hxScale,(ConstructionCutArithmetic.sum_contains ha hb hs).1 nx hnxa⟩
    · obtain ⟨_,nx,hxScale,hnxb⟩ := (hdb x).mp hxB
      exact (hdc x).mpr ⟨hxQ,nx,hxScale,(ConstructionCutArithmetic.sum_contains ha hb hs).2 nx hnxb⟩
    · obtain ⟨_,nu,hnu,hnua⟩ := (hda u).mp huda
      obtain ⟨_,nv,hnv,hnvb⟩ := (hdb v).mp hvdb
      obtain ⟨nx,hNX⟩ := ConstructionFractionScaling.exists_times hM hw hn ((hQ x).mp hxQ)
      obtain ⟨ns,hNS⟩ := ConstructionFractionScaling.exists_times hM hw hn (ConstructionCutAssociativity.sum_fraction hUV)
      obtain ⟨sumN,hSumN⟩ := ConstructionFractionAddition.sum_exists hM hw
        (ConstructionFractionScaling.times_range hnu) (ConstructionFractionScaling.times_range hnv)
      have hSumNc := (hs sumN).mpr ⟨(hQ sumN).mpr (ConstructionCutAssociativity.sum_fraction hSumN),
        Or.inr (Or.inr ⟨nu,nv,sumN,hnua,hnvb,hSumN,ConstructionFractionOrder.le_refl hM hw (ConstructionCutAssociativity.sum_fraction hSumN)⟩)⟩
      have hScaleEq := times_sum_equiv hM hw hn hUV hnu hnv hNS hSumN
      have hNXNS := (ConstructionFractionScaling.order_iff hM hw hn hnp hNX hNS).mpr hXUV
      exact (hdc x).mpr ⟨hxQ,nx,hNX,hc.2.1 nx sumN hSumNc (ConstructionFractionOrder.le_trans hM hw hNXNS hScaleEq.1)⟩

/-- Pure invariant for the source single-coordinate gap estimate. All row,
code, cut and output parameters vary under native Raw induction. -/
def sumGapAt {m : Nat} (w Q R zero add Id q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
  (.imp (.mem (.bound 10) (.bound w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 9 10
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo 8 10 R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.bound 9)
  (.bound zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (PureKuratowskiProject.code
  (.bound 7) (.bound 8) (.bound zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  add.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6) (.imp (ConstructionProbeHomEvaluationSyntax.eval
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  add.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5) (.imp (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge 12 2 1)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge 11 2 0)) (Project.Formula.subset (.bound 1) (.bound 0))))))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge 9 4 3)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge 8 4 2)) (.imp (ConstructionRealCuts.cut
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1) (.imp (ConstructionCutAddition.sumCut
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 1 2) (.imp (ConstructionCutAddition.sumCut
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 1 0) (Project.Formula.subset (.bound 0) (.bound
  5))))))))))))))))))))))))))

theorem sumGapAt_freeClosed {m : Nat} (w Q R zero add Id q : Fin m) :
    (sumGapAt w Q R zero add Id q).FreeClosed := by
  simp -implicitDefEqProofs [sumGapAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed,
    ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem sumGapAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R zero add Id q : Fin m) :
    Project.Formula.satisfies env (sumGapAt w Q R zero add Id q) ↔
      ∀ n f g r y v i c d gap out, (Project.FirstOrderSemantics.reduct M).mem n (env.bound w) →
        MapsTo n (env.bound R) f → MapsTo n (env.bound R) g →
        PureKuratowski.Code M (env.bound q) f (env.bound zero) → PureKuratowski.Code M r g (env.bound zero) →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound add) (env.bound Id) (env.bound Id) (env.bound q) y →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound add) (env.bound Id) (env.bound Id) r v →
        (∀ j c0 d0, PureKuratowski.PairMember M j c0 f → PureKuratowski.PairMember M j d0 g → Subset c0 d0) →
        PureKuratowski.PairMember M i c f → PureKuratowski.PairMember M i d g →
        Cut hM (env.bound w) (env.bound Q) gap → SumCut hM (env.bound w) (env.bound Q) c gap d →
        SumCut hM (env.bound w) (env.bound Q) y gap out → Subset out v := by
  simp only [sumGapAt,ConstructionRealCuts.Subset,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeHomEvaluationSyntax.eval_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionCutAddition.sumCut_semantics hM]
  rfl

theorem sum_eval_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n f g q r y v i c d gap out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hf : MapsTo n R f) (hg : MapsTo n R g)
    (hq : PureKuratowski.Code M q f zero) (hr : PureKuratowski.Code M r g zero)
    (hy : Eval hM w R R R add Id Id q y) (hv : Eval hM w R R R add Id Id r v)
    (hmono : ∀ j c0 d0, PureKuratowski.PairMember M j c0 f → PureKuratowski.PairMember M j d0 g → Subset c0 d0)
    (hic : PureKuratowski.PairMember M i c f) (hid : PureKuratowski.PairMember M i d g)
    (hGap : Cut hM w Q gap) (hPoint : SumCut hM w Q c gap d) (hTotal : SumCut hM w Q y gap out) : Subset out v := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases zero (Fin.cases add (fun _ => Id))))),free := fun _ => w }
  let property : Project.UnarySchema 6 := {
    body := sumGapAt 1 2 3 4 5 6 0,freeClosed := sumGapAt_freeClosed _ _ _ _ _ _ _ }
  have he (q) : property.denote env q ↔ ∀ n f g r y v i c d gap out,
      (Project.FirstOrderSemantics.reduct M).mem n w → MapsTo n R f → MapsTo n R g →
      PureKuratowski.Code M q f zero → PureKuratowski.Code M r g zero →
      Eval hM w R R R add Id Id q y → Eval hM w R R R add Id Id r v →
      (∀ j c0 d0, PureKuratowski.PairMember M j c0 f → PureKuratowski.PairMember M j d0 g → Subset c0 d0) →
      PureKuratowski.PairMember M i c f → PureKuratowski.PairMember M i d g → Cut hM w Q gap →
      SumCut hM w Q c gap d → SumCut hM w Q y gap out → Subset out v :=
    sumGapAt_semantics hM (env.push q) 1 2 3 4 5 6 0
  have hall := ConstructionProbeEvaluationLaws.raw_induction hM env property hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro n f g r y v i c d gap out _ _ _ hq _ _ _ _ hic _ _ _ _
    have hfzero : f = zero := (PureKuratowski.code_injective hOld.2 hq).1.symm
    obtain ⟨pair,_,hpair⟩ := hic
    exact (hz pair (hfzero ▸ hpair)).elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro n f g r y v i c d gap out hn hf hg hq hr hy hv hmono hic hid hGap hPoint hTotal
    obtain ⟨a,ha,c0,hsc,hProd⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons hy
    have hscEq := ((hId s c0).mp hsc).2
    subst c0
    obtain ⟨k,m,pref,full,x,hk,hm,hSucc,hpref,hfull,hx,hs,ht,hcode,happend⟩ := hCons
    have hfx := PureKuratowski.code_injective hcode hq
    have hxzero : x = zero := hfx.2
    have hlen : n = m := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (hfx.1 ▸ ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hm) hfull)
    have hgm : MapsTo m R g := hlen ▸ hg
    obtain ⟨j,gpref,last,hd⟩ := SetTheory.Structure.IsFiniteSequenceLastDecomposition.exists_of_nonempty hZF
      (KuratowskiZF.interpretation hM) hw ⟨hm,ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hm) hgm⟩ ⟨k,hSucc.predecessor_mem⟩
    have hj := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1 (hw.members_areOrdinals hZF k hk) hSucc hd.length_successor
    subst j
    have hgpref : MapsTo k R gpref := ConstructionProbeRaw.maps_of_sequence hM hd.prefix_sequence.2
      (fun j c0 hjc => hgm.2 j c0 ((hd.prefix_restriction.2 j c0).mp hjc).2)
    obtain ⟨rpre,hrpre⟩ := KuratowskiZF.exists_code hM gpref zero
    have hConsR : ConstructionProbeRaw.Cons w R R last rpre r := ⟨k,m,gpref,g,zero,hk,hm,hSucc,hgpref,hgm,hxzero ▸ hx,
      hgm.2 k last hd.last_value,hrpre,hr,ConstructionProbeRaw.decomposition_append hM hgm hd⟩
    obtain ⟨b,hb,c0,hlastc,hProdR⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hConsR hv
    have hlastcEq := ((hId last c0).mp hlastc).2
    subst c0
    have hPrefMono : ∀ j c0 d0, PureKuratowski.PairMember M j c0 pref → PureKuratowski.PairMember M j d0 gpref → Subset c0 d0 := by
      intro j c0 d0 hjc hjd
      exact hmono j c0 d0 (hfx.1 ▸ (happend j c0).mpr (Or.inl hjc)) ((hd.prefix_restriction.2 j d0).mp hjd).2
    have hPrefixLe := (ConstructionMergerHeightComparison.sum_eval_comparison hM hw hz hzw hQ hR hId hAdd hk hpref hgpref
      (hxzero ▸ ht) hrpre ha hb hPrefMono).1
    have hLastLe := hmono k s last (hfx.1 ▸ (happend k s).mpr (Or.inr ⟨rfl,rfl⟩)) hd.last_value
    have hACut := (hR a).mp (ConstructionProbeHomEvaluation.eval_range hM ha)
    have hSCut := (hR s).mp hs
    have hLeftSum := ((hAdd s a y).mp hProd).2.2
    have hRightSum := ((hAdd last b v).mp hProdR).2.2
    rcases (happend i c).mp (hfx.1.symm ▸ hic) with hp | ⟨hi,hcEq⟩
    · have hi := ForcingConditionGraphs.function_input hpref.1 hp
      obtain ⟨prefPlus,_,hPrefPlus⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hACut hGap
      have hBound := (he t).mp ih k pref gpref rpre a b i c d gap prefPlus hk hpref hgpref
        (hxzero ▸ ht) hrpre ha hb hPrefMono hp ((hd.prefix_restriction.2 i d).mpr ⟨hi,hid⟩) hGap hPoint hPrefPlus
      have hOut := (ConstructionProbeIntervals.reassociate hM hw hQ hSCut hACut hGap hLeftSum hPrefPlus).mp hTotal
      exact ConstructionCutArithmetic.sum_mono hOut hRightSum hLastLe hBound
    · have hidk : PureKuratowski.PairMember M k d g := by simpa only [hi] using hid
      have hdEq := ForcingConditionGraphs.function_unique hgm.1 hidk hd.last_value
      have hPointLast : SumCut hM w Q s gap last := by simpa only [hcEq,hdEq] using hPoint
      have hOut := (ConstructionProbeIntervals.reassociate hM hw hQ hACut hSCut hGap
        (ConstructionCutArithmetic.sum_comm hM hw hLeftSum) hPointLast).mp hTotal
      exact ConstructionCutArithmetic.sum_mono (ConstructionCutArithmetic.sum_comm hM hw hOut) hRightSum (fun _ h => h) hPrefixLe)
  exact (he q).mp (hall q (ConstructionProbeHomEvaluation.eval_raw hM hy)) n f g r y v i c d gap out hn hf hg hq hr hy hv hmono hic hid hGap hPoint hTotal

/-- Construct the actual coordinate difference, its /n value and the actual
average difference. The required inequality is between those SAME values. -/
theorem coordinate_average_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n CH z t a b i c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j n)
    (hmono : ∀ j c0 d0, Product CH j z c0 → Product CH j t d0 → Subset c0 d0)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH t b)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i n) (hc : Product CH i z c) (hd : Product CH i t d) :
    ∃ gap part avgGap, Cut hM w Q gap ∧ ConstructionCutDifference.Value hM w Q c d gap ∧ SumCut hM w Q c gap d ∧
      Cut hM w Q part ∧ ConstructionCutDivision.Value hM w Q n gap part ∧
      Cut hM w Q avgGap ∧ ConstructionCutDifference.Value hM w Q a b avgGap ∧ SumCut hM w Q a avgGap b ∧ Subset part avgGap := by
  obtain ⟨sumZ,hSumZ,hDivZ⟩ := ha
  obtain ⟨sumT,hSumT,hDivT⟩ := hb
  obtain ⟨f,q,hf,hRowF,hq,hEvalZ⟩ := hSumZ
  obtain ⟨g,r,hg,hRowG,hr,hEvalT⟩ := hSumT
  have hic := (hRowF i c).mpr ⟨hi,hc⟩
  have hid := (hRowG i d).mpr ⟨hi,hd⟩
  have hRowMono : ∀ j c0 d0, PureKuratowski.PairMember M j c0 f → PureKuratowski.PairMember M j d0 g → Subset c0 d0 :=
    fun j c0 d0 hjc hjd => hmono j c0 d0 ((hRowF j c0).mp hjc).2 ((hRowG j d0).mp hjd).2
  have hSumZCut := (hR sumZ).mp (ConstructionProbeHomEvaluation.eval_range hM hEvalZ)
  have hSumTCut := (hR sumT).mp (ConstructionProbeHomEvaluation.eval_range hM hEvalT)
  have hSumLe := (ConstructionMergerHeightComparison.sum_eval_comparison hM hw hz hzw hQ hR hId hAdd hn hf hg hq hr hEvalZ hEvalT hRowMono).1
  have hAvgLe := (ConstructionCutDivision.order_iff hw hQ hn hnp hSumZCut hSumTCut hDivZ hDivT).mpr hSumLe
  have hACut := ConstructionCutDivision.value_cut hw hQ hn hnp hSumZCut hDivZ
  have hBCut := ConstructionCutDivision.value_cut hw hQ hn hnp hSumTCut hDivT
  have hCCut := (hR c).mp (hf.2 i c hic)
  have hDCut := (hR d).mp (hg.2 i d hid)
  obtain ⟨gap,hGapCut,hGapValue,hPointSum,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hCCut hDCut (hmono i c d hc hd)
  obtain ⟨part,hPartDiv⟩ := ConstructionCutDivision.exists_value hM w Q n gap
  have hPartCut := ConstructionCutDivision.value_cut hw hQ hn hnp hGapCut hPartDiv
  obtain ⟨avgGap,hAvgGapCut,hAvgGapValue,hAvgSum,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hACut hBCut hAvgLe
  obtain ⟨out,hOutCut,hOutSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hSumZCut hGapCut
  have hOutLe := sum_eval_gap hM hw hz hzw hQ hR hId hAdd hn hf hg hq hr hEvalZ hEvalT hRowMono hic hid hGapCut hPointSum hOutSum
  obtain ⟨outDiv,hOutDiv⟩ := ConstructionCutDivision.exists_value hM w Q n out
  have hMeanOutSum := division_sum hM hw hQ hn hnp hSumZCut hGapCut hOutSum hDivZ hPartDiv hOutDiv
  have hOutDivLe := (ConstructionCutDivision.order_iff hw hQ hn hnp hOutCut hSumTCut hOutDiv hDivT).mpr hOutLe
  have hPartLe := (ConstructionCutDifference.sum_le_iff hM hw hQ hPartCut hAvgGapCut hACut
    (ConstructionCutArithmetic.sum_comm hM hw hMeanOutSum) (ConstructionCutArithmetic.sum_comm hM hw hAvgSum)).mp hOutDivLe
  exact ⟨gap,part,avgGap,hGapCut,hGapValue,hPointSum,hPartCut,hPartDiv,hAvgGapCut,hAvgGapValue,hAvgSum,hPartLe⟩

/-- Source copiesHeight_gap, under the existing old weighted-parent and
literal coordinate/copy contracts; no new monotonicity or gap oracle. -/
theorem copiesHeight_gap (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n CH D mul e P C L projection A Height Cost top z t a b i c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j n)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection) (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hUniform : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul Height Cost)
    (hGraph : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH t b)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i n) (hzc : Product CH i z c) (htd : Product CH i t d)
    (hReach : ConstructionMergerCopyCones.Reaches D A z t) :
    ∃ gap part avgGap, Cut hM w Q gap ∧ ConstructionCutDifference.Value hM w Q c d gap ∧ SumCut hM w Q c gap d ∧
      Cut hM w Q part ∧ ConstructionCutDivision.Value hM w Q n gap part ∧
      Cut hM w Q avgGap ∧ ConstructionCutDifference.Value hM w Q a b avgGap ∧ SumCut hM w Q a avgGap b ∧ Subset part avgGap := by
  have hOldOrder := ConstructionProbeParent.height_order hM hm hc hR hHeight hHB hUniform
  exact coordinate_average_gap hM hw hz hzw hQ hR hId hAdd hn hnp
    (fun j c0 d0 hjc hjd => ConstructionMergerCoordinateLaws.coordHeight_mono hm hC hp hEq hCopy hz hOldOrder hGraph hjc hjd hReach)
    ha hb hi hzc htd

end PPAC.Migration.ConstructionMergerAverageGap
