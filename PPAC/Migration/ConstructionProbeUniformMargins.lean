/- Pinned ProbeMargins.Word.uniform_margin:450.
Use the EXISTING formula-indexed Raw induction for all internal lengths.
All four source cases consume accepted literal Word/height/cost producers. -/
import PPAC.Migration.ConstructionProbeSameHeadMargin
import PPAC.Migration.ConstructionProbeNewOldMargin
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionProbeUniformMargins
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Old Cons)
open ConstructionProbeGates (HeadSome)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeLetterIntervals (UniformAt UniformMargins)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Actual object formula, varying every compared word and both height values. -/
def atTarget {m : Nat} (w Q W G HL LC z : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE
    (.imp (.mem (.bound (2 : Fin (m+3))) (.bound W.succ.succ.succ))
    (.imp (.mem (.bound z.succ.succ.succ) (.bound W.succ.succ.succ))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge HL.succ.succ.succ 2 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge HL.succ.succ.succ z.succ.succ.succ 0))
    (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ G.succ.succ.succ 2 z.succ.succ.succ))
    (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ G.succ.succ.succ z.succ.succ.succ 2)))
      (ConstructionProbeIntervalsSyntax.uniformAt w.succ.succ.succ Q.succ.succ.succ W.succ.succ.succ
        G.succ.succ.succ LC.succ.succ.succ 2 z.succ.succ.succ 1 0)))))))))

theorem atTarget_freeClosed {m : Nat} (w Q W G HL LC z : Fin m) : (atTarget w Q W G HL LC z).FreeClosed := by
  simp -implicitDefEqProofs [atTarget,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeIntervalsSyntax.uniformAt_freeClosed]

theorem atTarget_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q W G HL LC z : Fin m) :
    Project.Formula.satisfies env (atTarget w Q W G HL LC z) ↔
      ∀ x hx hz, (Project.FirstOrderSemantics.reduct M).mem x (env.bound W) →
        (Project.FirstOrderSemantics.reduct M).mem (env.bound z) (env.bound W) →
        PureKuratowski.PairMember M x hx (env.bound HL) →
        PureKuratowski.PairMember M (env.bound z) hz (env.bound HL) →
        Divides (env.bound W) (env.bound G) x (env.bound z) →
        ¬ Divides (env.bound W) (env.bound G) (env.bound z) x →
        UniformAt hM (env.bound w) (env.bound Q) (env.bound W) (env.bound G) (env.bound LC) x (env.bound z) hx hz := by
  simp only [atTarget,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeIntervalsSyntax.uniformAt_semantics hM,
    Project.Term.eval_bound]
  rfl

/-- Source UniformMargin.trans, on the actual nonnegative-cut witnesses. -/
theorem uniform_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q W G LC x mid z hx hm hzv : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hHX : Cut hM w Q hx) (hHM : Cut hM w Q hm)
    (hLeft : UniformAt hM w Q W G LC x mid hx hm)
    (hRight : UniformAt hM w Q W G LC mid z hm hzv) : UniformAt hM w Q W G LC x z hx hzv := by
  obtain ⟨c1,s1,hC1,hS1,hStrict1,hMiss1⟩ := hLeft
  obtain ⟨c2,s2,hC2,hS2,hStrict2,hMiss2⟩ := hRight
  obtain ⟨bound,hBound,hMax⟩ := ConstructionCutArithmetic.exists_max hM hw hQ hC1 hC2
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHX hBound
  have hXMid : Subset hx hm := fun p hp => hStrict1.1 p
    ((ConstructionCutArithmetic.sum_contains hHX hC1 hS1).1 p hp)
  have hMidZ : Subset hm hzv := fun p hp => hStrict2.1 p
    ((ConstructionCutArithmetic.sum_contains hHM hC2 hS2).1 p hp)
  have hNewStrict : ConstructionProbeIntervals.Strict sum hzv := by
    rcases ConstructionCutArithmetic.max_cases hM hw hQ hC1 hC2 hMax with he | he
    · subst bound
      have heSum := ConstructionCutAddition.sum_unique hM hSum hS1
      subst sum
      exact ⟨fun p hp => hMidZ p (hStrict1.1 p hp),
        fun h => hStrict1.2 (fun p hp => h p (hMidZ p hp))⟩
    · subst bound
      exact ConstructionProbeIntervals.le_strict_trans
        (ConstructionCutArithmetic.sum_mono hSum hS2 hXMid (fun _ h => h)) hStrict2
  refine ⟨bound,sum,hBound,hSum,hNewStrict,?_⟩
  intro d cd hd hdc hdz hdx
  by_cases hdm : Divides W G d mid
  · exact fun p hp => (hMax p).mpr (Or.inl (hMiss1 d cd hd hdc hdm hdx p hp))
  · exact fun p hp => (hMax p).mpr (Or.inr (hMiss2 d cd hd hdc hdz hdm p hp))

/-- The full source uniform margin, not an external-depth or fixed-code theorem. -/
theorem uniform_margin (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul S A b zero W Emb H C Off V B F K E one u unit four e G unitW I HL LC Cap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hW : WordCarrier w D S mul A b W)
    (hMult : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unitW) (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hOff : MapsTo S R Off) (hV : MapsTo S R V) (hB : MapsTo S R B)
    (hHL : MapsTo W R HL) (hLC : MapsTo W R LC) (hCap : MapsTo W R Cap)
    (hFloor : ConstructionProbeLetterFloor.FloorLaws D S A K H F)
    (hCostBounds : ConstructionProbeCostBounds.CostBounds hM w Q D mul S A K H C F)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hHeight : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hCost : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hHB : ConstructionCutWeights.RangeBound unit HL) (hCB : ConstructionProbeGateCap.Bounds unit LC)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hConservative : ConstructionProbeConservative.Conservative D W mul G Emb) :
    UniformMargins hM w Q W G HL LC := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult hOld
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  have hExit := ConstructionProbeConditionalJoins.gate_existence hM hw hz hzw hm hAlpha hW hb hMult hUnit hOld hJoins hConservative
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hMult hUnit hOld hJoins hConservative
  obtain ⟨Gen,hGenMap,hGenGraph⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hCon hW hb hne hUnit
  have hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d := by
    intro s d hsd
    have hs := ForcingConditionGraphs.function_input hV.1 hsd
    obtain ⟨o,hso,_⟩ := hOff.1.2 s hs
    obtain ⟨bound,hsb,_⟩ := hB.1.2 s hs
    obtain ⟨_,_,_,_,_,_,_,_,hi,_⟩ := hI s o d bound hso hsd hsb
    exact hi.2.2.2.1
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases W (Fin.cases G (Fin.cases HL (fun _ => LC))))),free := fun _ => w }
  let p : Project.UnarySchema 6 := { body := atTarget 1 2 3 4 5 6 0,freeClosed := atTarget_freeClosed _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ∀ x hx hq, (Project.FirstOrderSemantics.reduct M).mem x W → (Project.FirstOrderSemantics.reduct M).mem q W →
        PureKuratowski.PairMember M x hx HL → PureKuratowski.PairMember M q hq HL →
        Divides W G x q → ¬ Divides W G q x → UniformAt hM w Q W G LC x q hx hq :=
    atTarget_semantics hM (env.push q) 1 2 3 4 5 6 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro oldY q hOldY
    apply (he q).mpr
    intro x hx hq hxW hqW hxh hqh hxq hqx
    have hyo := (hOld oldY q).mpr hOldY
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw (ConstructionProbeWord.word_raw hW hxW) with ⟨oldX,hOldX⟩ | ⟨t,Y,hXCons⟩
    · have hxo := (hOld oldX x).mpr hOldX
      exact ConstructionProbeCostMargins.uniform_margin_old hM hw hz hzw hW hm hmW hCon hEmb hOld hC hCap hCapG hCost hHeight hDiv hGates hUniform
        hxo hyo hxh hqh ((hDiv oldX oldY x q hxo hyo).mp hxq) (fun h => hqx ((hDiv oldY oldX q x hyo hxo).mpr h))
    · exact ConstructionProbeNewOldMargin.uniform_margin_new_old hM hw hz hzw hQ hR hu hone hunit hm hCon hAlpha hb hne hW hMult hUnit hEmb hOld hH hC hB hHL hCap hHB hI hHeight hCapG hCost hUniform hJoins hConservative
        hxW ⟨Y,hXCons⟩ hyo hxq hxh hqh) (by
    intro s Z q hTarget ih
    apply (he q).mpr
    intro x hx hq hxW hqW hxh hqh hxq hqx
    have hZW := (hW Z).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hTarget).mp ((hW q).mp hqW)).1
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw (ConstructionProbeWord.word_raw hW hxW) with ⟨oldX,hOldX⟩ | ⟨t,Y,hXCons⟩
    · exact ConstructionProbeOldNewMargin.uniform_margin_old_new hM hw hz hzw hQ hR hu hone hunit hm hmW hCon hW hEmb hOld hH hC hF hV hB hHL hCap hFloor hCostBounds hI hHeight hCapG hCost hCB hEmbed hExit
        ((hOld oldX x).mpr hOldX) hqW ⟨Z,hTarget⟩ hxq hxh hqh
    · by_cases hts : t = s
      · subst t
        have hYW := (hW Y).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hXCons).mp ((hW x).mp hxW)).1
        obtain ⟨gen,hgen,_⟩ := hGenMap.1.2 s (ConstructionProbeRawAction.cons_letter hTarget)
        have hGenCons := (hGenGraph s gen).mp hgen
        have hGenW := hGenMap.2 s gen hgen
        have hYZ := (ConstructionProbeSameHeadMargin.cons_dvd_cons_iff hM hw hz hzw hm hAlpha hW hb hMult hUnit hGenCons hGenW hXCons hTarget hxW hqW).mp hxq
        have hZYnot : ¬ Divides W G Z Y := fun h => hqx
          ((ConstructionProbeSameHeadMargin.cons_dvd_cons_iff hM hw hz hzw hm hAlpha hW hb hMult hUnit hGenCons hGenW hTarget hXCons hqW hxW).mpr h)
        obtain ⟨hy,hYH,_⟩ := hHL.1.2 Y hYW
        obtain ⟨hzv,hZH,_⟩ := hHL.1.2 Z hZW
        have hSuffix := (he Z).mp ih Y hy hzv hYW hZW hYH hZH hYZ hZYnot
        exact ConstructionProbeSameHeadMargin.uniform_margin_same_head hM hw hz hzw hQ hR hm hCon hAlpha hb hne hW hMult hUnit hOld hOff hV hHL hLC hVP hHeight hCost hExit
          hXCons hTarget hxW hqW hYH hZH hxh hqh hSuffix
      · have hDifferent : ¬ HeadSome w D S x s := fun h => hts (ConstructionProbeGates.head_unique hM hw ⟨Y,hXCons⟩ h)
        obtain ⟨g,og,hgOld,hxg,hgq⟩ := ConstructionProbeProfiles.old_factor_of_other_block hM hw hz hzw hm hAlpha hW hb hMult hUnit hExit
          hxW hqW hDifferent ⟨Z,hTarget⟩ hxq
        have hgo := (hOld g og).mpr hgOld
        have hogW := ConstructionProbeOldEmbedding.old_word hM hz hzw hW hgOld
        obtain ⟨hmid,hMid,_⟩ := hHL.1.2 og hogW
        have hLeft := ConstructionProbeNewOldMargin.uniform_margin_new_old hM hw hz hzw hQ hR hu hone hunit hm hCon hAlpha hb hne hW hMult hUnit hEmb hOld hH hC hB hHL hCap hHB hI hHeight hCapG hCost hUniform hJoins hConservative
          hxW ⟨Y,hXCons⟩ hgo hxg hxh hMid
        have hRight := ConstructionProbeOldNewMargin.uniform_margin_old_new hM hw hz hzw hQ hR hu hone hunit hm hmW hCon hW hEmb hOld hH hC hF hV hB hHL hCap hFloor hCostBounds hI hHeight hCapG hCost hCB hEmbed hExit
          hgo hqW ⟨Z,hTarget⟩ hgq hMid hqh
        exact uniform_trans hM hw hQ ((hR hx).mp (hHL.2 x hx hxh)) ((hR hmid).mp (hHL.2 og hmid hMid)) hLeft hRight)
  intro x z hx hzv hxh hzh hxz hzx
  have hxW := ForcingConditionGraphs.function_input hHL.1 hxh
  have hzW := ForcingConditionGraphs.function_input hHL.1 hzh
  exact (he z).mp (hAll z (ConstructionProbeWord.word_raw hW hzW)) x hx hzv hxW hzW hxh hzh hxz hzx

end PPAC.Migration.ConstructionProbeUniformMargins
