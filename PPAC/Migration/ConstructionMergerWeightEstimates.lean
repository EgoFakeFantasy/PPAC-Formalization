/- Pinned MergerCones.copiesHeight_pos:199, copiesCost_pos:246,
copiesCost_le_cap:253 and copiesCost_le_copy:267. Consumer: copiesHeightCost.
Use the UNCHANGED pure-formula Raw induction/evaluator and existing cut
arithmetic. All internal finite lengths; no host well-foundedness or new
fold/sequence/recursion backend. Full uniform margin is a later obligation. -/
import PPAC.Migration.ConstructionMergerFiniteWeights

namespace PPAC.Migration.ConstructionMergerWeightEstimates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset CutCarrier)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeHomEvaluation (Eval)
open ConstructionMergerFiniteWeights (CoordinateEval HeightValue CostValue)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def productBoundsAt {m : Nat} (w R op Id seed q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 1) (.bound seed.succ.succ))
  (.imp (ConstructionProbeGateCap.bounds seed.succ.succ 1) (.imp (ConstructionProbeHomEvaluationSyntax.eval
  w.succ.succ R.succ.succ R.succ.succ R.succ.succ op.succ.succ Id.succ.succ Id.succ.succ q.succ.succ 0) (.conj
  (.existsE (.mem (.bound 0) (.bound 1))) (.conj (Project.Formula.subset (.bound 0) (.bound seed.succ.succ))
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 3 1 0)) (Project.Formula.subset
  (.bound 2) (.bound 0))))))))))))

theorem productBoundsAt_freeClosed {m : Nat} (w R op Id seed q : Fin m) :
    (productBoundsAt w R op Id seed q).FreeClosed := by
  simp -implicitDefEqProofs [productBoundsAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem productBoundsAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w R op Id seed q : Fin m) :
    Project.Formula.satisfies env (productBoundsAt w R op Id seed q) ↔
      ∀ f y, PureKuratowski.Code M (env.bound q) f (env.bound seed) →
        ConstructionProbeGateCap.Bounds (env.bound seed) f →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound op) (env.bound Id) (env.bound Id) (env.bound q) y →
        (∃ p, (Project.FirstOrderSemantics.reduct M).mem p y) ∧ Subset y (env.bound seed) ∧
          ∀ i c, PureKuratowski.PairMember M i c f → Subset y c := by
  simp only [productBoundsAt,ConstructionRealCuts.Subset,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.code_correct hM,
    KuratowskiZF.source_edge,ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

def sumContainsAt {m : Nat} (w R op Id seed q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 1) (.bound seed.succ.succ))
  (.imp (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ R.succ.succ R.succ.succ R.succ.succ op.succ.succ
  Id.succ.succ Id.succ.succ q.succ.succ 0) (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge 3 1 0)) (Project.Formula.subset (.bound 0) (.bound 2)))))))))

theorem sumContainsAt_freeClosed {m : Nat} (w R op Id seed q : Fin m) :
    (sumContainsAt w R op Id seed q).FreeClosed := by
  simp -implicitDefEqProofs [sumContainsAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem sumContainsAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w R op Id seed q : Fin m) :
    Project.Formula.satisfies env (sumContainsAt w R op Id seed q) ↔
      ∀ f y, PureKuratowski.Code M (env.bound q) f (env.bound seed) →
        Eval hM (env.bound w) (env.bound R) (env.bound R) (env.bound R) (env.bound op) (env.bound Id) (env.bound Id) (env.bound q) y →
        ∀ i c, PureKuratowski.PairMember M i c f → Subset c y := by
  simp only [sumContainsAt,ConstructionRealCuts.Subset,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.code_correct hM,
    KuratowskiZF.source_edge,ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

theorem product_eval_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero op Id one u top q f y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (htop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hOp : ConstructionCutProduct.Graph hM w Q R op)
    (hcode : PureKuratowski.Code M q f top) (hb : ConstructionProbeGateCap.Bounds top f)
    (hy : Eval hM w R R R op Id Id q y) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p y) ∧ Subset y top ∧
      ∀ i c, PureKuratowski.PairMember M i c f → Subset y c := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases w (Fin.cases R (Fin.cases op (Fin.cases Id (fun _ => top)))), free := fun _ => w }
  let p : Project.UnarySchema 5 := {
    body := productBoundsAt 1 2 3 4 5 0,
    freeClosed := productBoundsAt_freeClosed _ _ _ _ _ _ }
  have he (q) := productBoundsAt_semantics hM (env.push q) 1 2 3 4 5 0
  have hall := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro f y hcode _ hy
    have hfx := PureKuratowski.code_injective hOld.2 hcode
    have hxy := ((hId x y).mp (ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld hy)).2
    have hytop : y = top := hxy.symm.trans hfx.2
    rw [hytop]
    refine ⟨htop,fun _ h => h,?_⟩
    intro i c hic
    obtain ⟨a,_,ha⟩ := hic
    exact (hz a (hfx.1.symm ▸ ha)).elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro f y hcode hb hy
    obtain ⟨v,hv,a,has,hprod⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons hy
    have hae := ((hId s a).mp has).2
    subst a
    obtain ⟨n,m,pref,g,x,_,_,_,_,_,_,hs,ht,hq,happend⟩ := hCons
    have hfx := PureKuratowski.code_injective hq hcode
    have hbG : ConstructionProbeGateCap.Bounds top g := hfx.1.symm ▸ hb
    have hbP : ConstructionProbeGateCap.Bounds top pref := fun i c hic => hbG i c ((happend i c).mpr (Or.inl hic))
    have hvb := (he t).mp ih pref v (hfx.2 ▸ ht) hbP hv
    have hsb := hbG n s ((happend n s).mpr (Or.inr ⟨rfl,rfl⟩))
    have hvCut := (hR v).mp (ConstructionProbeHomEvaluation.eval_range hM hv)
    have hsCut := (hR s).mp hs
    have hval := ((hOp s v y).mp hprod).2.2
    have hys := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit hsCut hval hvb.2.1
    have hyv := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit hvCut
      (ConstructionCutProduct.value_comm hM hw hval) hsb.2
    refine ⟨ConstructionCutProduct.value_nonempty hM hw hQ hsCut hvCut hval hsb.1 hvb.1,
      fun p hp => hvb.2.1 p (hyv p hp),?_⟩
    intro i c hic
    rcases (happend i c).mp (hfx.1.symm ▸ hic) with hp | ⟨_,rfl⟩
    · exact fun p hp' => hvb.2.2 i c hp p (hyv p hp')
    · exact hys)
  exact (he q).mp (hall q (ConstructionProbeHomEvaluation.eval_raw hM hy)) f y hcode hb hy

theorem sum_eval_contains (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero op Id q f y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hR : CutCarrier hM w Q R) (hId : ForcingConditionGraphs.IdentityGraph R Id)
    (hOp : ConstructionCutArithmetic.Graph hM w Q R op)
    (hcode : PureKuratowski.Code M q f zero) (hy : Eval hM w R R R op Id Id q y) :
    ∀ i c, PureKuratowski.PairMember M i c f → Subset c y := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases w (Fin.cases R (Fin.cases op (Fin.cases Id (fun _ => zero)))), free := fun _ => w }
  let p : Project.UnarySchema 5 := {
    body := sumContainsAt 1 2 3 4 5 0,
    freeClosed := sumContainsAt_freeClosed _ _ _ _ _ _ }
  have he (q) := sumContainsAt_semantics hM (env.push q) 1 2 3 4 5 0
  have hall := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro f y hcode _ i c hic
    have hfx := PureKuratowski.code_injective hOld.2 hcode
    obtain ⟨a,_,ha⟩ := hic
    exact (hz a (hfx.1.symm ▸ ha)).elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro f y hcode hy
    obtain ⟨v,hv,a,has,hprod⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons hy
    have hae := ((hId s a).mp has).2
    subst a
    obtain ⟨n,m,pref,g,x,_,_,_,_,_,_,hs,ht,hq,happend⟩ := hCons
    have hfx := PureKuratowski.code_injective hq hcode
    have hvb := (he t).mp ih pref v (hfx.2 ▸ ht) hv
    have hvCut := (hR v).mp (ConstructionProbeHomEvaluation.eval_range hM hv)
    have hsCut := (hR s).mp hs
    have hval := ((hOp s v y).mp hprod).2.2
    have hsy := (ConstructionCutArithmetic.sum_contains hsCut hvCut hval).1
    have hvy := (ConstructionCutArithmetic.sum_contains hsCut hvCut hval).2
    intro i c hic
    rcases (happend i c).mp (hfx.1.symm ▸ hic) with hp | ⟨_,rfl⟩
    · exact fun p hp' => hvy p (hvb i c hp p hp')
    · exact hsy)
  exact (he q).mp (hall q (ConstructionProbeHomEvaluation.eval_raw hM hy)) f y hcode hy

theorem coordinate_product_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R zero op Id one u top CC z y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (htop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hOp : ConstructionCutProduct.Graph hM w Q R op)
    (hb : ∀ i z c, Product CC i z c → (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c top)
    (hy : CoordinateEval hM w n R op Id top CC z y) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p y) ∧ Subset y top ∧
      ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i n → Product CC i z c → Subset y c := by
  obtain ⟨f,q,_,hrow,hcode,hy⟩ := hy
  have hf : ConstructionProbeGateCap.Bounds top f := fun i c hic => hb i z c ((hrow i c).mp hic).2
  have h := product_eval_bounds hM hw hz hzw hQ hR hu hone hunit htop hId hOp hcode hf hy
  exact ⟨h.1,h.2.1,fun i c hi hc => h.2.2 i c ((hrow i c).mpr ⟨hi,hc⟩)⟩

theorem coordinate_sum_contains (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R zero op Id CH z y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hR : CutCarrier hM w Q R) (hId : ForcingConditionGraphs.IdentityGraph R Id)
    (hOp : ConstructionCutArithmetic.Graph hM w Q R op)
    (hy : CoordinateEval hM w n R op Id zero CH z y) :
    ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i n → Product CH i z c → Subset c y := by
  obtain ⟨f,q,_,hrow,hcode,hy⟩ := hy
  exact fun i c hi hc => sum_eval_contains hM hw hz hzw hR hId hOp hcode hy i c ((hrow i c).mpr ⟨hi,hc⟩)

/-- The witness is supplied by the actual prescribed-copy quotient, not a
new positivity/representation oracle. -/
theorem copiesHeight_positive (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R zero add Id CH z a D mul P C L projection Height top : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mul P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hCH : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hzL : (Project.FirstOrderSemantics.reduct M).mem z L)
    (ha : HeightValue hM w Q n R add Id zero CH z a) : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a := by
  obtain ⟨sum,hSum,hDiv⟩ := ha
  obtain ⟨i,x,hi,hx,hproj⟩ := ConstructionMergerCopies.representative hC hL hProj hzL
  obtain ⟨c,hc,_⟩ := hHeight.1.2 x hx
  have hcoord := (ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hCH hproj).mpr hc
  have hcSum := coordinate_sum_contains hM hw hz hzw hR hId hAdd hSum i c hi hcoord
  obtain ⟨p,hp⟩ := (hHB x c hc).1
  exact (ConstructionCutDivision.nonempty_iff hw hQ hn hnp
    ((hR sum).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSum)) hDiv).mpr ⟨p,hcSum p hp⟩

/-- Exact copiesCost_pos / le_cap / le_copy estimates. Bounds for EVERY
coordinate are retained, independent of the representative of the letter. -/
theorem copiesCost_estimates (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R zero op Id one u top CC z a cap J L : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (htop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top)
    (hId : ForcingConditionGraphs.IdentityGraph R Id) (hOp : ConstructionCutProduct.Graph hM w Q R op)
    (hJ : Representatives n L J) (hCC : MapsTo J R CC)
    (hb : ∀ i z c, Product CC i z c → (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c top)
    (hcap : (Project.FirstOrderSemantics.reduct M).mem cap R)
    (hcapN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p cap)
    (ha : CostValue hM w Q n R op Id top cap CC z a) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) ∧
      (∀ b, ConstructionCutDivision.Value hM w Q n cap b → Subset a b) ∧
      (∀ i c b, Product CC i z c → ConstructionCutDivision.Value hM w Q n c b → Subset a b) := by
  obtain ⟨prod,limited,hProd,hMin,hDiv⟩ := ha
  have hProdBounds := coordinate_product_bounds hM hw hz hzw hQ hR hu hone hunit htop hId hOp hb hProd
  have hProdCut := (hR prod).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hProd)
  have hcapCut := (hR cap).mp hcap
  have hLimitedCut : ConstructionRealCuts.Cut hM w Q limited := by
    rcases ConstructionCutMinimum.value_cases hM hw hQ hcapCut hProdCut hMin with rfl | rfl
    · exact hcapCut
    · exact hProdCut
  refine ⟨(ConstructionCutDivision.nonempty_iff hw hQ hn hnp hLimitedCut hDiv).mpr
    (ConstructionCutMinimum.value_nonempty hM hw hQ hcapCut hProdCut hMin hcapN hProdBounds.1),?_,?_⟩
  · intro b hb
    exact (ConstructionCutDivision.order_iff hw hQ hn hnp hLimitedCut hcapCut hDiv hb).mpr
      (ConstructionCutMinimum.value_bounds hMin).1
  · intro i c b hc hb
    have hi := (ConstructionProbeAction.projected_indices hJ hCC hc).1
    have hcCut := (hR c).mp (ConstructionProbeAction.projected_range hCC hc)
    exact (ConstructionCutDivision.order_iff hw hQ hn hnp hLimitedCut hcCut hDiv hb).mpr
      (fun p hp => hProdBounds.2.2 i c hi hc p ((ConstructionCutMinimum.value_bounds hMin).2 p hp))

/-- Compose the actual coordinate bounds, the old unit-height cap and the
finite estimates. No new positivity or coordinate-bound oracle is assumed. -/
theorem copies_estimates (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R zero add mulCut Id one u top CH CC D mulOld P C L projection Height Cost J e unitHeight two cap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (hId : ForcingConditionGraphs.IdentityGraph R Id)
    (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hMul : ConstructionCutProduct.Graph hM w Q R mulCut)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mulOld P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mulOld P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mulOld P projection)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hCH : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hCoordC : ConstructionMergerCoordinates.Graph n L projection Cost top CC)
    (hJ : Representatives n L J) (hCC : MapsTo J R CC)
    (hEdge : PureKuratowski.PairMember M e unitHeight Height)
    (htwo : (Project.FirstOrderSemantics.reduct M).SuccessorOf two one)
    (htwow : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hCap : ConstructionCutDivision.Value hM w Q two unitHeight cap) :
    ∀ z a, (Project.FirstOrderSemantics.reduct M).mem z L →
      (HeightValue hM w Q n R add Id zero CH z a → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) ∧
      (CostValue hM w Q n R mulCut Id top cap CC z a →
        (∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) ∧
        (∀ b, ConstructionCutDivision.Value hM w Q n cap b → Subset a b) ∧
        ∀ i x c b, Product projection i x z → PureKuratowski.PairMember M x c Cost →
          ConstructionCutDivision.Value hM w Q n c b → Subset a b) := by
  have hOldCut := (hR unitHeight).mp (hHeight.2 e unitHeight hEdge)
  have hOldN := (hHB e unitHeight hEdge).1
  have htopN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top := by
    obtain ⟨p,hp⟩ := hOldN
    exact ⟨p,(hHB e unitHeight hEdge).2.1 p hp⟩
  have hcapR := (hR cap).mpr (ConstructionCutDivision.value_cut hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap)
  have hcapN := (ConstructionCutDivision.nonempty_iff hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap).mpr hOldN
  have hCostBounds := (ConstructionMergerCoordinateLaws.coordinate_bounds hz htopN hHB hCB hCH hCoordC).2
  intro z a hzL
  constructor
  · exact copiesHeight_positive hM hw hz hzw hQ hR hn hnp hId hAdd hC hL hp hProj hEq hHeight hHB hCH hzL
  · intro ha
    have h := copiesCost_estimates hM hw hz hzw hQ hR hn hnp hu hone hunit htopN hId hMul hJ hCC hCostBounds hcapR hcapN ha
    refine ⟨h.1,h.2.1,?_⟩
    intro i x c b hproj hcost hdiv
    exact h.2.2 i c b ((ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hCoordC hproj).mpr hcost) hdiv

end PPAC.Migration.ConstructionMergerWeightEstimates
