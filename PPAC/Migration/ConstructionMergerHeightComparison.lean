/- Pinned MergerCones.copiesHeight_strictMono:222 and sum comparison used
by copiesHeight_lt_one:211 / copiesHeight_gap:234. Reuse existing native
Raw induction, sequence last decomposition, cut addition strictness and
positive-integer division; source copiesCost_le_one:257 uses the same
natural-scaling inequality. All internal lengths; no new recursion backend. -/
import PPAC.Migration.ConstructionMergerWeightEstimates
import PPAC.Migration.ConstructionCutDifference

namespace PPAC.Migration.ConstructionMergerHeightComparison
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
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

theorem sum_step_comparison (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q s t a b y v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hs : Cut hM w Q s) (ht : Cut hM w Q t) (ha : Cut hM w Q a) (hb : Cut hM w Q b)
    (hy : ConstructionCutAddition.SumCut hM w Q s a y) (hv : ConstructionCutAddition.SumCut hM w Q t b v)
    (hst : Subset s t) (hab : Subset a b) : Subset y v ∧ ((Strict s t ∨ Strict a b) → Strict y v) := by
  have hle := ConstructionCutArithmetic.sum_mono hy hv hst hab
  refine ⟨hle,?_⟩
  obtain ⟨mid,_,hmid⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hs hb
  intro h
  rcases h with h | h
  · exact ConstructionProbeIntervals.le_strict_trans
      (ConstructionCutArithmetic.sum_mono hy hmid (fun _ h => h) hab)
      ((ConstructionCutDifference.sum_strict_iff hM hw hQ hs ht hb hmid hv).mpr h)
  · have hymid := (ConstructionCutDifference.sum_strict_iff hM hw hQ ha hb hs
      (ConstructionCutArithmetic.sum_comm hM hw hy) (ConstructionCutArithmetic.sum_comm hM hw hmid)).mpr h
    have hmidv := ConstructionCutArithmetic.sum_mono hmid hv hst (fun _ h => h)
    exact ⟨hle,fun hrev => hymid.2 (fun p hp => hrev p (hmidv p hp))⟩

def sumCompareAt {m : Nat} (w R add Id zero q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 5) (.bound
  w.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 4 5
  R.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 3 5
  R.succ.succ.succ.succ.succ.succ)) (.imp (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ.succ.succ)
  (.bound 4) (.bound zero.succ.succ.succ.succ.succ.succ)) (.imp (PureKuratowskiProject.code (.bound 2) (.bound 3)
  (.bound zero.succ.succ.succ.succ.succ.succ)) (.imp (ConstructionProbeHomEvaluationSyntax.eval
  w.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ add.succ.succ.succ.succ.succ.succ Id.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ 1) (.imp
  (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ add.succ.succ.succ.succ.succ.succ
  Id.succ.succ.succ.succ.succ.succ Id.succ.succ.succ.succ.succ.succ 2 0) (.imp (.forallE (.forallE (.forallE
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 7 2 1)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge 6 2 0)) (Project.Formula.subset (.bound 1) (.bound 0))))))) (.conj
  (Project.Formula.subset (.bound 1) (.bound 0)) (.imp (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.edge 7 2 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 6 2 0)) (.conj
  (Project.Formula.subset (.bound 1) (.bound 0)) (.neg (Project.Formula.subset (.bound 0) (.bound 1)))))))))
  (.conj (Project.Formula.subset (.bound 1) (.bound 0)) (.neg (Project.Formula.subset (.bound 0) (.bound
  1))))))))))))))))))))

theorem sumCompareAt_freeClosed {m : Nat} (w R add Id zero q : Fin m) :
    (sumCompareAt w R add Id zero q).FreeClosed := by
  simp -implicitDefEqProofs [sumCompareAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem sumCompareAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w R add Id zero q : Fin m) :
    Project.Formula.satisfies env (sumCompareAt w R add Id zero q) ↔
      ∀ n f g r y v, (Project.FirstOrderSemantics.reduct M).mem n (env.bound w) →
        MapsTo n (env.bound R) f → MapsTo n (env.bound R) g →
        PureKuratowski.Code M (env.bound q) f (env.bound zero) → PureKuratowski.Code M r g (env.bound zero) →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound add) (env.bound Id) (env.bound Id) (env.bound q) y →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound add) (env.bound Id) (env.bound Id) r v →
        (∀ i a b, PureKuratowski.PairMember M i a f → PureKuratowski.PairMember M i b g → Subset a b) →
        Subset y v ∧ ((∃ i a b, PureKuratowski.PairMember M i a f ∧ PureKuratowski.PairMember M i b g ∧ Strict a b) → Strict y v) := by
  simp only [sumCompareAt,ConstructionRealCuts.Subset,ConstructionProbeIntervals.Strict,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    KuratowskiZF.code_correct hM,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

theorem sum_eval_comparison (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n f g q r y v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hf : MapsTo n R f) (hg : MapsTo n R g)
    (hq : PureKuratowski.Code M q f zero) (hr : PureKuratowski.Code M r g zero)
    (hy : Eval hM w R R R add Id Id q y) (hv : Eval hM w R R R add Id Id r v)
    (hmono : ∀ i a b, PureKuratowski.PairMember M i a f → PureKuratowski.PairMember M i b g → Subset a b) :
    Subset y v ∧ ((∃ i a b, PureKuratowski.PairMember M i a f ∧ PureKuratowski.PairMember M i b g ∧ Strict a b) → Strict y v) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases w (Fin.cases R (Fin.cases add (Fin.cases Id (fun _ => zero)))),free := fun _ => w }
  let p : Project.UnarySchema 5 := {
    body := sumCompareAt 1 2 3 4 5 0,freeClosed := sumCompareAt_freeClosed _ _ _ _ _ _ }
  have he (q) := sumCompareAt_semantics hM (env.push q) 1 2 3 4 5 0
  dsimp only [env,SetTheory.Env.push] at he
  have hall := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro n f g r y v hn hf hg hq hr hy hv _
    have hfx := PureKuratowski.code_injective hOld.2 hq
    have hxzero : x = zero := hfx.2
    have hfzero : f = zero := hfx.1.symm
    have hlen : n = zero := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (hfzero.symm ▸ SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
    have hgzero : g = zero := SetTheory.Structure.IsFiniteSequenceOfLength.empty_sequence_unique hZF.1
      ⟨hn,ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hg⟩
      ⟨hzw,SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz⟩
      (hlen.symm ▸ hz) hz
    have hyzero : y = zero := ((hId x y).mp (ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld hy)).2.symm.trans hfx.2
    have hrzero : PureKuratowski.Code M r g zero := hr
    have hOldR : ConstructionProbeRaw.Old zero R zero r := ⟨hxzero ▸ hOld.1,by simpa only [hgzero] using hrzero⟩
    have hvzero : v = zero := ((hId zero v).mp (ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOldR hv)).2.symm
    refine ⟨fun t ht => hvzero.symm ▸ hyzero ▸ ht,?_⟩
    rintro ⟨i,a,b,hia,_,_⟩
    obtain ⟨pair,_,hp⟩ := hia
    exact (hz pair (hfzero ▸ hp)).elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro n f g r y v hn hf hg hq hr hy hv hmono
    obtain ⟨a,ha,c,hsc,hProd⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons hy
    have hscEq := ((hId s c).mp hsc).2
    subst c
    obtain ⟨k,m,pref,full,x,hk,hm,hSucc,hpref,hfull,hx,hs,ht,hcode,happend⟩ := hCons
    have hfx := PureKuratowski.code_injective hcode hq
    have hxzero : x = zero := hfx.2
    have hlen : n = m := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (hfx.1 ▸ ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hm) hfull)
    have hgm : MapsTo m R g := hlen ▸ hg
    obtain ⟨j,gpref,d,hd⟩ := SetTheory.Structure.IsFiniteSequenceLastDecomposition.exists_of_nonempty hZF
      (KuratowskiZF.interpretation hM) hw ⟨hm,ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hm) hgm⟩ ⟨k,hSucc.predecessor_mem⟩
    have hj := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1 (hw.members_areOrdinals hZF k hk) hSucc hd.length_successor
    subst j
    have hgpref : MapsTo k R gpref := ConstructionProbeRaw.maps_of_sequence hM hd.prefix_sequence.2
      (fun i c hic => hgm.2 i c ((hd.prefix_restriction.2 i c).mp hic).2)
    obtain ⟨rpre,hrpre⟩ := KuratowskiZF.exists_code hM gpref zero
    have hConsR : ConstructionProbeRaw.Cons w R R d rpre r := ⟨k,m,gpref,g,zero,hk,hm,hSucc,hgpref,hgm,hxzero ▸ hx,
      hgm.2 k d hd.last_value,hrpre,hr,ConstructionProbeRaw.decomposition_append hM hgm hd⟩
    obtain ⟨b,hb,c,hdc,hProdR⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hConsR hv
    have hdcEq := ((hId d c).mp hdc).2
    subst c
    have hPrefMono : ∀ i c d, PureKuratowski.PairMember M i c pref → PureKuratowski.PairMember M i d gpref → Subset c d := by
      intro i c d hic hid
      exact hmono i c d (hfx.1 ▸ (happend i c).mpr (Or.inl hic)) ((hd.prefix_restriction.2 i d).mp hid).2
    have hih := (he t).mp ih k pref gpref rpre a b hk hpref hgpref (hxzero ▸ ht) hrpre ha hb hPrefMono
    have hLastMono := hmono k s d (hfx.1 ▸ (happend k s).mpr (Or.inr ⟨rfl,rfl⟩)) hd.last_value
    have hStep := sum_step_comparison hM hw hQ ((hR s).mp hs) ((hR d).mp (hgm.2 k d hd.last_value))
      ((hR a).mp (ConstructionProbeHomEvaluation.eval_range hM ha)) ((hR b).mp (ConstructionProbeHomEvaluation.eval_range hM hb))
      ((hAdd s a y).mp hProd).2.2 ((hAdd d b v).mp hProdR).2.2 hLastMono hih.1
    refine ⟨hStep.1,?_⟩
    rintro ⟨i,c,d',hic,hid,hstrict⟩
    rcases (happend i c).mp (hfx.1.symm ▸ hic) with hp | ⟨rfl,rfl⟩
    · have hi := ForcingConditionGraphs.function_input hpref.1 hp
      exact hStep.2 (Or.inr (hih.2 ⟨i,c,d',hp,(hd.prefix_restriction.2 i d').mpr ⟨hi,hid⟩,hstrict⟩))
    · have hdEq := ForcingConditionGraphs.function_unique hgm.1 hid hd.last_value
      exact hStep.2 (Or.inl (hdEq ▸ hstrict)))
  exact (he q).mp (hall q (ConstructionProbeHomEvaluation.eval_raw hM hy)) n f g r y v hn hf hg hq hr hy hv hmono

theorem coordinate_sum_comparison (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n CH z t y v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hy : CoordinateEval hM w n R add Id zero CH z y) (hv : CoordinateEval hM w n R add Id zero CH t v)
    (hmono : ∀ i a b, Product CH i z a → Product CH i t b → Subset a b) :
    Subset y v ∧ ((∃ i a b, (Project.FirstOrderSemantics.reduct M).mem i n ∧
      Product CH i z a ∧ Product CH i t b ∧ Strict a b) → Strict y v) := by
  obtain ⟨f,q,hf,hRowF,hq,hy⟩ := hy
  obtain ⟨g,r,hg,hRowG,hr,hv⟩ := hv
  have h := sum_eval_comparison hM hw hz hzw hQ hR hId hAdd hn hf hg hq hr hy hv
    (fun i a b ha hb => hmono i a b ((hRowF i a).mp ha).2 ((hRowG i b).mp hb).2)
  refine ⟨h.1,?_⟩
  rintro ⟨i,a,b,hi,ha,hb,hs⟩
  exact h.2 ⟨i,a,b,(hRowF i a).mpr ⟨hi,ha⟩,(hRowG i b).mpr ⟨hi,hb⟩,hs⟩

/-- Literal source strict monotonicity on the SAME prescribed copies and
finite-average graph. Existing old UniformMargins supplies coordinate
strictness; actual quotient representation supplies a strict coordinate. -/
theorem copiesHeight_order (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add Id n CH z t a b D mul e P C L projection A Height Cost top J : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mul P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hJ : Representatives n L J) (hCH : MapsTo J R CH)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hUniform : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul Height Cost)
    (hGraph : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hzL : (Project.FirstOrderSemantics.reduct M).mem z L) (htL : (Project.FirstOrderSemantics.reduct M).mem t L)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH t b)
    (hReach : ConstructionMergerCopyCones.Reaches D A z t) : Subset a b ∧ (z ≠ t → Strict a b) := by
  obtain ⟨sumZ,hSumZ,hDivZ⟩ := ha
  obtain ⟨sumT,hSumT,hDivT⟩ := hb
  have hOrder := ConstructionProbeParent.height_order hM hm hc hR hHeight hHB hUniform
  have hCompare := coordinate_sum_comparison hM hw hz hzw hQ hR hId hAdd hn hSumZ hSumT
    (fun i c d hzc htd => ConstructionMergerCoordinateLaws.coordHeight_mono hm hC hp hEq hCopy hz hOrder hGraph hzc htd hReach)
  have hzCut := (hR sumZ).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSumZ)
  have htCut := (hR sumT).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSumT)
  refine ⟨(ConstructionCutDivision.order_iff hw hQ hn hnp hzCut htCut hDivZ hDivT).mpr hCompare.1,?_⟩
  intro hne
  obtain ⟨i,x,hi,_,hrep⟩ := ConstructionMergerCopies.representative hC hL hProj hzL
  obtain ⟨c,_,hzc⟩ := ConstructionProbeAction.projected hM hJ hCH hi hzL
  obtain ⟨d,_,htd⟩ := ConstructionProbeAction.projected hM hJ hCH hi htL
  have hstrict := ConstructionMergerCoordinateLaws.coordHeight_strict hM hm hc hC hp hEq hCopy hR hHeight hUniform hGraph hzc htd hReach hne ⟨x,hrep⟩
  exact (ConstructionCutDivision.strict_iff hw hQ hn hnp hzCut htCut hDivZ hDivT).mpr
    (hCompare.2 ⟨i,c,d,hi,hzc,htd,hstrict⟩)

/-- Positive internal naturals are at least the canonical internal one. -/
theorem one_le_positive (hM : FirstOrder.Theory.Models M nativeZF)
    {w one n : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p n) : ConstructionFractionOrder.NatLe one n := by
  rcases ConstructionFractionOrder.nat_compare hM hw ho hn with he | hlt | hlt
  · exact Or.inl he
  · exact Or.inr hlt
  · obtain ⟨zero,hzero,hs⟩ := hone
    rcases (hs n).mp hlt with h | h
    · exact (hzero n h).elim
    · obtain ⟨p,hp⟩ := hnp
      exact (hzero p ((h p).mp hp)).elim

/-- The needed natural-scaling inequality; no general real-field extension. -/
theorem times_ge (hM : FirstOrder.Theory.Models M nativeZF)
    {w one n q r : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p n)
    (hr : ConstructionFractionScaling.Times hM w n q r) : ConstructionFractionOrder.Le hM w q r := by
  obtain ⟨a,b,an,hq,hmul,hr⟩ := hr
  apply (ConstructionBaseHeightGap.same_den_le hM hw hq hr).mpr
  by_cases ha : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a
  · exact (ConstructionFractionOrder.mul_le_iff hM hw hq.1 ha ho hn
      (ConstructionFractionOrder.mul_one hM hw hq.1 ho hone).1 hmul).mpr (one_le_positive hM hw ho hone hn hnp)
  · have hEmpty : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p a := fun p hp => ha ⟨p,hp⟩
    have hProdEmpty := ZF.ordinalMultiplication_empty_left (ModelTransfer.project_models_iff.mp hM)
      (KuratowskiZF.interpretation hM) hEmpty n (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) n hn) an hmul
    exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members a an (fun p => iff_of_false (hEmpty p) (hProdEmpty p)))

theorem division_subset (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q one n a c : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p n)
    (ha : Cut hM w Q a) (hc : ConstructionCutDivision.Value hM w Q n a c) : Subset c a := by
  intro q hq
  obtain ⟨_,r,hr,hra⟩ := (hc q).mp hq
  exact ha.2.1 q r hra (times_ge hM hw ho hone hn hnp hr)

/-- Source copiesCost_le_one:257, in fact strict under the original old
height bound. The actual min/old-unit-height/2/n formula supplies the bound;
no additional cost-bound or positive-cost oracle is required. -/
theorem copiesCost_unit_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R one n two D Height e unitHeight top cap mulCut Id CC z a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p n)
    (htwo : (Project.FirstOrderSemantics.reduct M).SuccessorOf two one)
    (htwow : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hEdge : PureKuratowski.PairMember M e unitHeight Height)
    (hCap : ConstructionCutDivision.Value hM w Q two unitHeight cap)
    (ha : ConstructionMergerFiniteWeights.CostValue hM w Q n R mulCut Id top cap CC z a) : Strict a top := by
  have hOldCut := (hR unitHeight).mp (hHeight.2 e unitHeight hEdge)
  have hCapCut := ConstructionCutDivision.value_cut hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap
  have hCapLe := division_subset hM hw ho hone htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap
  obtain ⟨prod,limited,hProd,hMin,hDiv⟩ := ha
  have hProdCut := (hR prod).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hProd)
  have hLimitedCut : Cut hM w Q limited := by
    rcases ConstructionCutMinimum.value_cases hM hw hQ hCapCut hProdCut hMin with rfl | rfl
    · exact hCapCut
    · exact hProdCut
  have hLimitedLe := (ConstructionCutMinimum.value_bounds hMin).1
  have hCostLe := division_subset hM hw ho hone hn hnp hLimitedCut hDiv
  exact ConstructionProbeIntervals.le_strict_trans
    (fun p hp => hCapLe p (hLimitedLe p (hCostLe p hp))) (hHB e unitHeight hEdge).2

end PPAC.Migration.ConstructionMergerHeightComparison
