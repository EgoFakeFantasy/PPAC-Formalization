/- Pinned MergerCones.wordHeight:371 / wordHeight_bounds:389.
Reuse the UNCHANGED Raw evaluator, affine operation and bound invariant.
The carrier is actual Merger Raw, not the Probe-specific WordCarrier.
Rotate the affine expression back to the literal source v+(1-v)*theta. -/
import PPAC.Migration.ConstructionMergerWordParameters
import PPAC.Migration.ConstructionProbeWeightBounds

namespace PPAC.Migration.ConstructionMergerWordHeights
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeRaw (Raw Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeHomEvaluation (Eval)
open ConstructionProbeHomEvaluationSyntax (LiftGraph)
open ConstructionProbeHeightOperation (Affine)
open ConstructionProbeHeightFold (Laws)
open ConstructionMergerWordParameters (Recipe)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Apply the existing native function constructor to the unchanged evaluator.
Only the source carrier premise is adapted from Probe Word to literal Raw. -/
theorem raw_lift_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J G H Id W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hG : MapsTo J N G) (hH : MapsTo D N H) (hId : MapsTo S N Id)
    (hW : ConstructionProbeRaw.Carrier w D S W) :
    ∃ L, MapsTo W N L ∧ LiftGraph hM w D S N G H Id W L := by
  let schema : Project.BinarySchema 7 := {
    body := ConstructionProbeHomEvaluationSyntax.eval 2 3 4 5 6 7 8 1 0
    freeClosed := ConstructionProbeHomEvaluationSyntax.eval_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases N (Fin.cases G (Fin.cases H (fun _ => Id)))))), free := fun _ => w }
  have he (q y : M.Carrier .set) : schema.denote env q y ↔ Eval hM w D S N G H Id q y :=
    ConstructionProbeHomEvaluationSyntax.eval_semantics hM ((env.push q).push y) 2 3 4 5 6 7 8 1 0
  obtain ⟨L,hL,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := W) (target := N) (by
      intro q hq
      obtain ⟨y,hy⟩ := ConstructionProbeHomEvaluation.eval_total hM hw hJ hG hH hId ((hW q).mp hq)
      exact ⟨y,(he q y).mpr hy⟩) (by
      intro q _ y z hy hz
      exact ConstructionProbeHomEvaluation.eval_unique hM hw hJ hG hH hId ((he _ _).mp hy) ((he _ _).mp hz)) (by
      intro q y _ hy
      exact ConstructionProbeHomEvaluation.eval_range hM ((he _ _).mp hy))
  exact ⟨L,(ForcingSupportSize.native_mapsTo hM W N L).mpr hL,
    fun q y => (hGraph q y).trans (and_congr_right (fun _ => he q y))⟩

theorem raw_height_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W Q R H O V N J G Id L : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hSN : Subset S N) (hRN : Subset R N)
    (hJ : Representatives N N J) (hG : MapsTo J R G) (hGN : MapsTo J N G)
    (hH : MapsTo D R H) (hHN : MapsTo D N H) (hId : MapsTo S N Id)
    (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeHeightOperation.Graph hM w Q R S zero O V N G)
    (hl : LiftGraph hM w D S N G H Id W L) : Laws hM w D S zero W Q H O V L := by
  constructor
  · intro x q y hOld
    constructor
    · exact fun hy => ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld ((hl q y).mp hy).2
    · intro hy
      exact (hl q y).mpr ⟨(hW q).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOld),
        (ConstructionProbeHomEvaluation.eval_old_iff hM hw hz hzw hJ hGN hHN hId hOld).mpr hy⟩
  · intro s t q y hCons hqW
    have htW := (hW t).mpr (ConstructionProbeRaw.cons_raw hCons).1
    have hs := ConstructionProbeRawAction.cons_letter hCons
    constructor
    · intro hy
      obtain ⟨v,hv,hprep⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons ((hl q y).mp hy).2
      exact ⟨v,(hl t v).mpr ⟨htW,hv⟩,
        (ConstructionProbeHeightFold.prepend_iff hM hSN hRN hi hg hs (ConstructionProbeHeightFold.eval_range hM hH hG hv)).mp hprep⟩
    · rintro ⟨v,hv,ha⟩
      have hvEval := ((hl t v).mp hv).2
      exact (hl q y).mpr ⟨hqW,(ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hGN hHN hId hCons).mpr
        ⟨v,hvEval,(ConstructionProbeHeightFold.prepend_iff hM hSN hRN hi hg hs (ConstructionProbeHeightFold.eval_range hM hH hG hvEval)).mpr ha⟩⟩

theorem exists_height (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W Q R H O V : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hZeroR : (Project.FirstOrderSemantics.reduct M).mem zero R)
    (hH : MapsTo D R H) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hW : ConstructionProbeRaw.Carrier w D S W) :
    ∃ L, MapsTo W R L ∧ Laws hM w D S zero W Q H O V L := by
  obtain ⟨N,hN⟩ := KP.exists_unionOfTwo (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S R
  have hSN : Subset S N := fun s hs => (hN s).mpr (Or.inl hs)
  have hRN : Subset R N := fun r hr => (hN r).mpr (Or.inr hr)
  obtain ⟨J,G,hJ,hG,hg⟩ := ConstructionProbeHeightOperation.exists_operation hM hw hQ hR hO hV hZeroR N
  have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hRN y (hG.2 p y hy)⟩
  have hHN : MapsTo D N H := ⟨hH.1,fun x y hy => hRN y (hH.2 x y hy)⟩
  obtain ⟨Id,hIdPerm,hi⟩ := ForcingConditionGraphs.exists_identity hM S
  have hId : MapsTo S N Id := ⟨hIdPerm.1.1,fun x y hy => hSN y (hIdPerm.1.2 x y hy)⟩
  obtain ⟨L,hL,hl⟩ := raw_lift_graph hM hw hJ hGN hHN hId hW
  have hLR : MapsTo W R L := ⟨hL.1,fun q y hy => ConstructionProbeHeightFold.eval_range hM hH hG ((hl q y).mp hy).2⟩
  exact ⟨L,hLR,raw_height_laws hM hw hz hzw hW hSN hRN hJ hG hGN hH hHN hId hi hg hl⟩

/-- The existing affine bound invariant, on actual Merger Raw and source parameters. -/
theorem height_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W H HD CD O V B HL unit one u four quarter eighth : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hHL : MapsTo W R HL)
    (hO : MapsTo S R O) (hV : MapsTo S R V) (hB : MapsTo S R B)
    (hOB : ConstructionCutWeights.RangeBound unit O)
    (hVP : ∀ s sigma, PureKuratowski.PairMember M s sigma V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma)
    (hParams : ∀ s theta sigma factor, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V →
      PureKuratowski.PairMember M s factor B → Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor)
    (hHB : ConstructionCutWeights.RangeBound unit H)
    (hLaws : Laws hM w D S zero W Q H O V HL) : ConstructionCutWeights.RangeBound unit HL := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases unit (fun _ => HL), free := fun _ => w }
  let p : Project.UnarySchema 2 := {
    body := ConstructionProbeWeightBounds.boundAt 1 2 0
    freeClosed := ConstructionProbeWeightBounds.boundAt_freeClosed _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔ ∀ y,
      PureKuratowski.PairMember M q y HL → ConstructionCutWeights.BoundedPositive y unit :=
    ConstructionProbeWeightBounds.boundAt_semantics hM (env.push q) 1 2 0
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    exact (he q).mpr (fun y hy => hHB x y ((hLaws.1 x q y hOld).mp hy))) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro y hy
    have hq := ForcingConditionGraphs.function_input hHL.1 hy
    obtain ⟨v,htv,theta,sigma,prod,hso,hsd,hProd,hSum⟩ := (hLaws.2 s t q y hCons hq).mp hy
    have hv := (hR v).mp (hHL.2 t v htv)
    have hTheta := (hR theta).mp (hO.2 s theta hso)
    have hSigma := (hR sigma).mp (hV.2 s sigma hsd)
    have hs := ConstructionProbeRawAction.cons_letter hCons
    obtain ⟨factor,hb,_⟩ := hB.1.2 s hs
    obtain ⟨ah,ac,qh,qc,_,_,_,_,_,_,hComp,_⟩ := hParams s theta sigma factor hso hsd hb
    have hProdCut := ConstructionCutProduct.value_cut hM hw hQ hSigma hv hProd
    have hSmall := ConstructionCutProductArithmetic.positive_strict hM hw hQ hSigma hv hUnit (hVP s sigma hsd)
      ((he t).mp ih v htv).2 hProd (ConstructionCutProductUnit.right_unit hM hw hQ hu hone hunit hSigma)
    have hStrict := (ConstructionCutDifference.sum_strict_iff hM hw hQ hProdCut hSigma hTheta
      (ConstructionCutArithmetic.sum_comm hM hw hSum) (ConstructionCutArithmetic.sum_comm hM hw hComp)).mpr hSmall
    obtain ⟨r,hr⟩ := (hOB s theta hso).1
    exact ⟨⟨r,(ConstructionCutArithmetic.sum_contains hTheta hProdCut hSum).1 r hr⟩,hStrict⟩)
  intro q y hy
  exact (he q).mp (hAll q ((hW q).mp (ForcingConditionGraphs.function_input hHL.1 hy))) y hy

/-- v+(1-v)*theta = theta+(1-theta)*v by EXISTING cut distributivity. -/
theorem rotate_affine (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q one u unit theta sigma v room p out y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hTheta : Cut hM w Q theta) (hSigma : Cut hM w Q sigma) (hv : Cut hM w Q v) (hRoom : Cut hM w Q room)
    (hComp : SumCut hM w Q theta sigma unit) (hVRoom : SumCut hM w Q v room unit)
    (hp : ConstructionCutProduct.Value hM w Q sigma v p) (hOut : ConstructionCutProduct.Value hM w Q room theta out)
    (hy : SumCut hM w Q theta p y) : SumCut hM w Q v out y := by
  obtain ⟨q,hqCut,hq⟩ := ConstructionCutProduct.exists_product hM hw hQ hTheta hv
  have hPCut := ConstructionCutProduct.value_cut hM hw hQ hSigma hv hp
  have hOutCut := ConstructionCutProduct.value_cut hM hw hQ hRoom hTheta hOut
  have hPQV := ConstructionCutProductArithmetic.distrib hM hw hQ hv hSigma hTheta
    (ConstructionCutArithmetic.sum_comm hM hw hComp) (ConstructionCutProduct.value_comm hM hw hp)
    (ConstructionCutProduct.value_comm hM hw hq) (ConstructionCutProductUnit.right_unit hM hw hQ hu hone hunit hv)
  have hQTTheta := ConstructionCutProductArithmetic.distrib hM hw hQ hTheta hv hRoom hVRoom hq
    (ConstructionCutProduct.value_comm hM hw hOut) (ConstructionCutProductUnit.right_unit hM hw hQ hu hone hunit hTheta)
  exact (ConstructionProbeIntervals.reassociate hM hw hQ hPCut hqCut hOutCut hPQV hQTTheta).mpr
    (ConstructionCutArithmetic.sum_comm hM hw hy)

def LiteralStep (hM : FirstOrder.Theory.Models M nativeZF) (w Q unit O letter v y : M.Carrier .set) : Prop :=
  ∃ theta room prod, PureKuratowski.PairMember M letter theta O ∧ Cut hM w Q room ∧
    ConstructionCutDifference.Value hM w Q v unit room ∧ SumCut hM w Q v room unit ∧
    ConstructionCutProduct.Value hM w Q room theta prod ∧ SumCut hM w Q v prod y

def literalStep {m : Nat} (w Q unit O letter v y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ letter.succ.succ.succ 2)) (.conj (ConstructionRealCuts.cut w.succ.succ.succ
  Q.succ.succ.succ 1) (.conj (ConstructionCutDifference.value w.succ.succ.succ Q.succ.succ.succ
  v.succ.succ.succ unit.succ.succ.succ 1) (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ
  Q.succ.succ.succ v.succ.succ.succ 1 unit.succ.succ.succ) (.conj (ConstructionCutProduct.value
  w.succ.succ.succ Q.succ.succ.succ 1 2 0) (ConstructionCutAddition.sumCut w.succ.succ.succ
  Q.succ.succ.succ v.succ.succ.succ 0 y.succ.succ.succ)))))))))

theorem literalStep_freeClosed {m : Nat} (w Q unit O letter v y : Fin m) :
    (literalStep w Q unit O letter v y).FreeClosed := by
  simp -implicitDefEqProofs [literalStep,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionRealCuts.cut_freeClosed,ConstructionCutDifference.value_freeClosed,
    ConstructionCutProduct.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem literalStep_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q unit O letter v y : Fin m) :
    Project.Formula.satisfies env (literalStep w Q unit O letter v y) ↔
      LiteralStep hM (env.bound w) (env.bound Q) (env.bound unit) (env.bound O) (env.bound letter) (env.bound v) (env.bound y) := by
  simp only [literalStep,LiteralStep,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionRealCuts.cut_semantics hM,ConstructionCutDifference.value_semantics hM,
    ConstructionCutProduct.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM]
  rfl

theorem affine_literal_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S one u unit O V letter v y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hComp : ∀ s theta sigma, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V → SumCut hM w Q theta sigma unit)
    (hs : (Project.FirstOrderSemantics.reduct M).mem letter S) (hv : Cut hM w Q v) (hvUnit : Subset v unit) :
    Affine hM w Q O V letter v y ↔ LiteralStep hM w Q unit O letter v y := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  constructor
  · rintro ⟨theta,sigma,p,ho,hsigma,hp,hy⟩
    have hTheta := (hR theta).mp (hO.2 letter theta ho)
    have hSigma := (hR sigma).mp (hV.2 letter sigma hsigma)
    obtain ⟨room,hRoom,hDiff,hVRoom,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ hv hUnit hvUnit
    obtain ⟨prod,_,hProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hRoom hTheta
    exact ⟨theta,room,prod,ho,hRoom,hDiff,hVRoom,hProd,
      rotate_affine hM hw hQ hu hone hunit hTheta hSigma hv hRoom (hComp letter theta sigma ho hsigma) hVRoom hp hProd hy⟩
  · rintro ⟨theta,room,prod,ho,hRoom,_,hVRoom,hProd,hSum⟩
    have hTheta := (hR theta).mp (hO.2 letter theta ho)
    obtain ⟨sigma,hsigma,_⟩ := hV.1.2 letter hs
    have hSigma := (hR sigma).mp (hV.2 letter sigma hsigma)
    obtain ⟨p,hPCut,hp⟩ := ConstructionCutProduct.exists_product hM hw hQ hSigma hv
    obtain ⟨y',_,hy'⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hTheta hPCut
    have hRotated := rotate_affine hM hw hQ hu hone hunit hTheta hSigma hv hRoom
      (hComp letter theta sigma ho hsigma) hVRoom hp hProd hy'
    have he := ConstructionCutAddition.sum_unique hM hRotated hSum
    exact he ▸ (show Affine hM w Q O V letter v y' from ⟨theta,sigma,p,ho,hsigma,hp,hy'⟩)

/-- Exact old and source snoc recurrence, on ALL internal words. -/
def LiteralLaws (hM : FirstOrder.Theory.Models M nativeZF) (w Q D S zero unit H O HL : M.Carrier .set) : Prop :=
  (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y HL ↔ PureKuratowski.PairMember M x y H)) ∧
  ∀ letter pref q y, Cons w D S letter pref q →
    (PureKuratowski.PairMember M q y HL ↔ ∃ v, PureKuratowski.PairMember M pref v HL ∧ LiteralStep hM w Q unit O letter v y)

def literalLaws {m : Nat} (w Q D S zero unit H O HL : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ
  D.succ.succ.succ 2 1) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge HL.succ.succ.succ 1
  0)) (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ 2 0))))))) (.forallE
  (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.cons w.succ.succ.succ.succ
  D.succ.succ.succ.succ S.succ.succ.succ.succ 3 2 1) (.iff (ProjectSyntax.encode id
  (Source.SetLanguage.edge HL.succ.succ.succ.succ 1 0)) (.existsE (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge HL.succ.succ.succ.succ.succ 3 0)) (literalStep w.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ 4 0
  1))))))))))

theorem literalLaws_freeClosed {m : Nat} (w Q D S zero unit H O HL : Fin m) :
    (literalLaws w Q D S zero unit H O HL).FreeClosed := by
  simp -implicitDefEqProofs [literalLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed,literalStep_freeClosed]

theorem literalLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D S zero unit H O HL : Fin m) :
    Project.Formula.satisfies env (literalLaws w Q D S zero unit H O HL) ↔
      LiteralLaws hM (env.bound w) (env.bound Q) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound unit) (env.bound H) (env.bound O) (env.bound HL) := by
  simp only [literalLaws,LiteralLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,literalStep_semantics hM]
  rfl

theorem literal_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W one u unit H O V HL : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hHL : MapsTo W R HL) (hHB : ConstructionCutWeights.RangeBound unit HL)
    (hComp : ∀ s theta sigma, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V → SumCut hM w Q theta sigma unit)
    (hLaws : Laws hM w D S zero W Q H O V HL) : LiteralLaws hM w Q D S zero unit H O HL := by
  refine ⟨hLaws.1,?_⟩
  intro letter pref q y hCons
  have hq := (hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2
  have hs := ConstructionProbeRawAction.cons_letter hCons
  constructor
  · intro hy
    obtain ⟨v,hv,hAffine⟩ := (hLaws.2 letter pref q y hCons hq).mp hy
    exact ⟨v,hv,(affine_literal_iff hM hw hQ hR hu hone hunit hO hV hComp hs ((hR v).mp (hHL.2 pref v hv)) (hHB pref v hv).2.1).mp hAffine⟩
  · rintro ⟨v,hv,hStep⟩
    exact (hLaws.2 letter pref q y hCons hq).mpr ⟨v,hv,
      (affine_literal_iff hM hw hQ hR hu hone hunit hO hV hComp hs ((hR v).mp (hHL.2 pref v hv)) (hHB pref v hv).2.1).mpr hStep⟩

end PPAC.Migration.ConstructionMergerWordHeights
