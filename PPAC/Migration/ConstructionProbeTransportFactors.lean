/- Pinned ProbePresentations.Word.transport_factor_of_dvd/transport_factors/transport_dvd_iff.
The existing shared gate supplies the exit branch; equal heads cancel the
existing letter action. The induction ranges over every internal Raw length. -/
import PPAC.Migration.ConstructionProbeSharedGates

namespace PPAC.Migration.ConstructionProbeTransportFactors
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (AlphabetSimulation FactorConservation DivisionReflection)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeWordTransport (WordGraph)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reflect the specified factor once source divisibility is known. -/
theorem transport_factor_of_dvd {W WN G GN unitN H x y X Y q : M.Carrier .set}
    (hmN : LeftCancelMonoid WN GN unitN) (hH : MapsTo W WN H) (hMul : PreservesProducts G GN H)
    (hX : PureKuratowski.PairMember M x X H) (hY : PureKuratowski.PairMember M y Y H)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q WN) (hprod : Product GN X q Y)
    (hxy : Divides W G x y) : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r W ∧ PureKuratowski.PairMember M r q H := by
  obtain ⟨r,hr,hxr⟩ := hxy
  obtain ⟨R,hR,_⟩ := hH.1.2 r hr
  have he : R = q := (hmN.2.1 X (hH.2 x X hX)).2.2 R q Y (hH.2 r R hR) hq
    (hMul x r y X R Y hxr hX hR hY) hprod
  exact ⟨r,hr,he ▸ hR⟩

def FactorsAt (W WN GN H x : M.Carrier .set) : Prop := ∀ y X Y q,
  PureKuratowski.PairMember M x X H → PureKuratowski.PairMember M y Y H →
  (Project.FirstOrderSemantics.reduct M).mem q WN → Product GN X q Y →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r W ∧ PureKuratowski.PairMember M r q H

def factorsAt {m : Nat} (W WN GN H x : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ x.succ.succ.succ.succ 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ 3 1)) (.imp (.mem (.bound 0) (.bound WN.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product GN.succ.succ.succ.succ 2 0 1)) (.existsE (.conj (.mem
  (.bound 0) (.bound W.succ.succ.succ.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ.succ 0 1))))))))))))

theorem factorsAt_freeClosed {m : Nat} (W WN GN H x : Fin m) : (factorsAt W WN GN H x).FreeClosed := by
  simp -implicitDefEqProofs [factorsAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem factorsAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W WN GN H x : Fin m) :
    Project.Formula.satisfies env (factorsAt W WN GN H x) ↔
      FactorsAt (env.bound W) (env.bound WN) (env.bound GN) (env.bound H) (env.bound x) := by
  simp only [factorsAt,FactorsAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M)]
  rfl

theorem transport_factors (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g H W WN E EN e eN I IN G GN unit unitN O ON : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : AlphabetSimulation S SN A AN E EN f g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN)
    (hH : Injection W WN H) (hGraph : WordGraph w D S SN f g W H) (hMul : PreservesProducts G GN H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∀ x, Raw w D S x → FactorsAt W WN GN H x := by
  have hbD := function_input hf.1.1.1 hb
  have hfbN := hf.1.1.2 b fb hb
  have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hf.1 hPres hf.2.1
  have hmWordN := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmN hAlphaN hWN hfbN hUnitN hGN
  have hGate := ConstructionProbeSharedGates.exists_simulated_gate_of_exit hM hw hz hzw hm hmN hAlpha hAlphaN
    hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH.1 hGraph hO hON hJ hA hC
  let schema : Project.UnarySchema 4 := {
    body := factorsAt 1 2 3 4 0
    freeClosed := factorsAt_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := Fin.cases W (Fin.cases WN (Fin.cases GN (fun _ => H))), free := fun _ => w }
  have he (x) : schema.denote env x ↔ FactorsAt W WN GN H x :=
    factorsAt_semantics hM (env.push x) 1 2 3 4 0
  have hAll : ∀ x, Raw w D S x → schema.denote env x := by
    apply ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw
    · intro a x hOld
      apply (he x).mpr
      intro y X Y q hX hY hq hprod
      have hyW := function_input hH.1.1 hY
      obtain ⟨fa,hfa,_⟩ := hf.1.1.1.2 a hOld.1
      have hOldN := ConstructionProbeRawTransport.transport_old hM hz hf.1.1 hOld hfa ((hGraph x X).mp hX).2
      have hHeadN := (old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN hOldN (hH.1.2 y Y hY)).mp ⟨q,hq,hprod⟩
      have hHead := (ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1
        hDiv hAlphabet.2.2.2 hfa ((hGraph y Y).mp hY).2).mp hHeadN
      exact transport_factor_of_dvd hmWordN hH.1 hMul hX hY hq hprod
        ((old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hbD hG hOld hyW).mpr hHead)
    · intro s t x hCons ih
      apply (he x).mpr
      intro y X Y q hX hY hq hprod
      have hxW := function_input hH.1.1 hX
      have hyW := function_input hH.1.1 hY
      have hred := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW x).mp hxW)
      have htW := (hW t).mpr hred.1
      obtain ⟨T,hT,_⟩ := hH.1.1.2 t htW
      obtain ⟨gs,hgs,_⟩ := hAlphabet.1.1.1.2 s (cons_letter hCons)
      have hConsN := ConstructionProbeRawTransport.transport_cons hM hw hf.1.1 hAlphabet.1.1 hCons hgs
        ((hGraph t T).mp hT).2 ((hGraph x X).mp hX).2
      by_cases hys : HeadSome w N SN Y gs
      · have hys' := (ConstructionProbeHeadTransport.head_transport_some hM hw hz hzw hf.1.1 hAlphabet.1
          ((hGraph y Y).mp hY).2 hgs).mp hys
        obtain ⟨z,hzW,hnotZ,hConsZ⟩ := (head_some_cons_iff hM hw hz hzw hW hyW).mp hys'
        obtain ⟨Z,hZ,_⟩ := hH.1.1.2 z hzW
        have hConsZN := ConstructionProbeRawTransport.transport_cons hM hw hf.1.1 hAlphabet.1.1 hConsZ hgs
          ((hGraph z Z).mp hZ).2 ((hGraph y Y).mp hY).2
        have hnotZN : ¬ HeadDiv w N SN zero mulN AN fb Z := fun h => hnotZ
          ((ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1
            hDiv hAlphabet.2.2.2 hb ((hGraph z Z).mp hZ).2).mp h)
        obtain ⟨Tq,hTq,hLetter⟩ := (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hmN hAlphaN hWN hfbN hConsN).mp
          ((hGN X q Y).mp hprod).2
        have hLetterZ : ConstructionProbeLetterAction.LetterAct w N SN zero mulN AN fb WN EN gs Z Y :=
          ⟨hAlphabet.1.1.2 s gs hgs,hH.1.2 z Z hZ,Or.inr ⟨hnotZN,hConsZN⟩⟩
        have heq := ConstructionProbeLetterAction.letterAct_injective hM hw hz hzw hmN hAlphaN hLetter hLetterZ
        subst Tq
        exact (he t).mp ih z T Z q hT hZ hq ((hGN T q Z).mpr ⟨hH.1.2 t T hT,hTq⟩)
      · obtain ⟨j,fj,_,hfj,hgate,hgateN⟩ := hGate x (word_raw hW hxW) X s gs Y hX hgs ⟨t,hCons⟩
          (hH.1.2 y Y hY) ⟨q,hq,hprod⟩ hys
        have hHeadN := (hgateN Y (hH.1.2 y Y hY)).mp ⟨⟨q,hq,hprod⟩,hys⟩
        have hHead := (ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1
          hDiv hAlphabet.2.2.2 hfj ((hGraph y Y).mp hY).2).mp hHeadN
        exact transport_factor_of_dvd hmWordN hH.1 hMul hX hY hq hprod (((hgate y hyW).mpr hHead).1)
  exact fun x hx => (he x).mp (hAll x hx)

theorem factor_conservation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g H W WN E EN e eN I IN G GN unit unitN O ON : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : AlphabetSimulation S SN A AN E EN f g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN)
    (hH : Injection W WN H) (hGraph : WordGraph w D S SN f g W H) (hMul : PreservesProducts G GN H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    FactorConservation WN GN H := by
  intro x y q X Y hX hY hq hprod
  obtain ⟨r,_,hr⟩ := transport_factors hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN
    hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC x (word_raw hW (function_input hH.1.1 hX)) y X Y q hX hY hq hprod
  exact ⟨r,hr⟩

theorem transport_dvd_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g H W WN E EN e eN I IN G GN unit unitN O ON : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : AlphabetSimulation S SN A AN E EN f g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN)
    (hH : Injection W WN H) (hGraph : WordGraph w D S SN f g W H) (hMul : PreservesProducts G GN H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    DivisionReflection W WN G GN H := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW (function_input hf.1.1.1 hb) hUnit hG
  have hmWN := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmN hAlphaN hWN (hf.1.1.2 b fb hb) hUnitN hGN
  exact ConstructionProbeAlphabetMap.division_reflection hmW hmWN hH hMul
    (factor_conservation hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN
      hH hGraph hMul hO hON hJ hA hC)

open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics)
open ConstructionProbeConservativeSyntax (conservative conservative_freeClosed conservative_semantics)
open ConstructionProbeOldEmbeddingSyntax (oldGraph oldGraph_freeClosed oldGraph_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordTransport (wordGraph wordGraph_freeClosed wordGraph_semantics)
open ConstructionProbeSharedIntersections (conditionalJoins conditionalJoins_freeClosed conditionalJoins_semantics)

open ConstructionProbeAlphabetMapSyntax (factorConservation factorConservation_freeClosed factorConservation_semantics)

def divisionReflection {m : Nat} (W WN G GN H : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 2
  0)) (.iff (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ
  GN.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ.succ
  G.succ.succ.succ.succ 3 2)))))))))

theorem divisionReflection_freeClosed {m : Nat} (W WN G GN H : Fin m) :
    (divisionReflection W WN G GN H).FreeClosed := by
  simp -implicitDefEqProofs [divisionReflection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem divisionReflection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W WN G GN H : Fin m) :
    Project.Formula.satisfies env (divisionReflection W WN G GN H) ↔
      DivisionReflection (env.bound W) (env.bound WN) (env.bound G) (env.bound GN) (env.bound H) := by
  simp only [divisionReflection,DivisionReflection,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def factorsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 29
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 29))) (.imp (Project.Formula.isEmpty (.bound (5 : Fin
    29))) (.imp (.mem (.bound (5 : Fin 29)) (.bound (0 : Fin 29))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 29) (6 : Fin 29) (19 : Fin 29))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 29) (7 : Fin 29) (20 : Fin 29)))
    (.imp (alphabet (1 : Fin 29) (6 : Fin 29) (19 : Fin 29) (3 : Fin 29) (21 : Fin 29) (8 : Fin 29) (17 : Fin
    29)) (.imp (alphabet (2 : Fin 29) (7 : Fin 29) (20 : Fin 29) (4 : Fin 29) (22 : Fin 29) (9 : Fin 29) (18 :
    Fin 29)) (.imp (conservative (1 : Fin 29) (2 : Fin 29) (6 : Fin 29) (7 : Fin 29) (12 : Fin 29)) (.imp
    (preservesProducts (6 : Fin 29) (7 : Fin 29) (12 : Fin 29)) (.imp (alphabetSimulation (3 : Fin 29) (4 :
    Fin 29) (8 : Fin 29) (9 : Fin 29) (17 : Fin 29) (18 : Fin 29) (12 : Fin 29) (13 : Fin 29)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 29) (10 : Fin 29) (11 : Fin 29))) (.imp
    (wordCarrier (0 : Fin 29) (1 : Fin 29) (3 : Fin 29) (6 : Fin 29) (8 : Fin 29) (10 : Fin 29) (15 : Fin 29))
    (.imp (wordCarrier (0 : Fin 29) (2 : Fin 29) (4 : Fin 29) (7 : Fin 29) (9 : Fin 29) (11 : Fin 29) (16 :
    Fin 29)) (.imp (multiplicationGraph (0 : Fin 29) (1 : Fin 29) (3 : Fin 29) (5 : Fin 29) (6 : Fin 29) (8 :
    Fin 29) (10 : Fin 29) (15 : Fin 29) (17 : Fin 29) (23 : Fin 29)) (.imp (multiplicationGraph (0 : Fin 29)
    (2 : Fin 29) (4 : Fin 29) (5 : Fin 29) (7 : Fin 29) (9 : Fin 29) (11 : Fin 29) (16 : Fin 29) (18 : Fin 29)
    (24 : Fin 29)) (.imp (old (5 : Fin 29) (1 : Fin 29) (19 : Fin 29) (25 : Fin 29)) (.imp (old (5 : Fin 29)
    (2 : Fin 29) (20 : Fin 29) (26 : Fin 29)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (14
    : Fin 29) (15 : Fin 29) (16 : Fin 29))) (.imp (wordGraph (0 : Fin 29) (1 : Fin 29) (3 : Fin 29) (4 : Fin
    29) (12 : Fin 29) (13 : Fin 29) (15 : Fin 29) (14 : Fin 29)) (.imp (preservesProducts (23 : Fin 29) (24 :
    Fin 29) (14 : Fin 29)) (.imp (oldGraph (5 : Fin 29) (1 : Fin 29) (27 : Fin 29)) (.imp (oldGraph (5 : Fin
    29) (2 : Fin 29) (28 : Fin 29)) (.imp (conditionalJoins (1 : Fin 29) (6 : Fin 29)) (.imp (conservative (1
    : Fin 29) (15 : Fin 29) (6 : Fin 29) (23 : Fin 29) (27 : Fin 29)) (.imp (conservative (2 : Fin 29) (16 :
    Fin 29) (7 : Fin 29) (24 : Fin 29) (28 : Fin 29)) (.conj (factorConservation (16 : Fin 29) (24 : Fin 29)
    (14 : Fin 29)) (divisionReflection (15 : Fin 29) (16 : Fin 29) (23 : Fin 29) (24 : Fin 29) (14 : Fin
    29))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,alphabetSimulation_freeClosed,conservative_freeClosed,preservesProducts_freeClosed,
      wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,wordGraph_freeClosed,oldGraph_freeClosed,
      conditionalJoins_freeClosed,factorConservation_freeClosed,divisionReflection_freeClosed]

theorem factors_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence factorsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) factorsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    alphabet_semantics hM,alphabetSimulation_semantics hM,conservative_semantics hM,preservesProducts_semantics hM,
    wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,wordGraph_semantics hM,
    oldGraph_semantics hM,conditionalJoins_semantics hM,factorConservation_semantics hM,divisionReflection_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC =>
    ⟨factor_conservation hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC,
      transport_dvd_iff hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC⟩

theorem factors_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence factorsSentence) := ModelTransfer.derives (fun _ hM => factors_models hM)

end PPAC.Migration.ConstructionProbeTransportFactors
