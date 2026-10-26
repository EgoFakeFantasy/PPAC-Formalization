/- Pinned ProbePresentations.Word.transport_old_common_below,
transport_dvd_of_different_head and transport_common_below.
Equal heads use the already proved generator/letterAct multiplication law in
its relational eval_letterAct form; no new generator or induction backend. -/
import PPAC.Migration.ConstructionProbeTransportFactors

namespace PPAC.Migration.ConstructionProbeTransportCommon
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeGatesSyntax (headSome headSome_freeClosed headSome_semantics gate gate_freeClosed gate_semantics)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_word old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (AlphabetSimulation)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins shared_intersections)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeWordTransport (WordGraph)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem transport_old_pair_below (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g H W WN E EN e eN I IN G GN O ON : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f)
    (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hH : MapsTo W WN H) (hGraph : WordGraph w D S SN f g W H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∀ a c fa fc q, PureKuratowski.PairMember M a fa f → PureKuratowski.PairMember M c fc f →
      (Project.FirstOrderSemantics.reduct M).mem q WN → HeadDiv w N SN zero mulN AN fa q → HeadDiv w N SN zero mulN AN fc q →
      ∃ j J, (Project.FirstOrderSemantics.reduct M).mem j W ∧ PureKuratowski.PairMember M j J H ∧
        HeadDiv w D S zero mul A a j ∧ HeadDiv w D S zero mul A c j ∧ Divides WN GN J q := by
  intro a c fa fc q hfa hfc hq haq hcq
  have hbD := function_input hf.1.1.1 hb
  have hfbN := hf.1.1.2 b fb hb
  obtain ⟨k,fk,hk,hfk,hjoin,hjoinN⟩ := ConstructionProbeSharedGates.shared_headDiv_intersection hM hw hz hzw
    hm hmN hAlpha hAlphaN hW hWN hbD hfbN hG hGN hO hON hJ hf hA hC hfa hfc hq haq hcq
  obtain ⟨j,hj⟩ := exists_old hM (zero := zero) hk
  have hjW := old_word hM hz hzw hW hj
  obtain ⟨J,hJmap,_⟩ := hH.1.2 j hjW
  have hOldN := ConstructionProbeRawTransport.transport_old hM hz hf.1.1 hj hfk ((hGraph j J).mp hJmap).2
  have hkk : HeadDiv w D S zero mul A k j :=
    (headDiv_old_iff hz hj).mpr ⟨e,hm.1.1,((hm.1.2 k hk k).2).mpr rfl⟩
  have hboth := (hjoin j hjW).mpr hkk
  exact ⟨j,J,hjW,hJmap,hboth.1,hboth.2,
    (old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN hOldN hq).mpr ((hjoinN q hq).mp ⟨haq,hcq⟩)⟩

theorem transport_old_common_below (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hH : MapsTo W WN H) (hGraph : WordGraph w D S SN f g W H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∀ a fa y Y q, PureKuratowski.PairMember M a fa f → PureKuratowski.PairMember M y Y H →
      (Project.FirstOrderSemantics.reduct M).mem q WN → HeadDiv w N SN zero mulN AN fa q → Divides WN GN Y q →
      ∃ j J, (Project.FirstOrderSemantics.reduct M).mem j W ∧ PureKuratowski.PairMember M j J H ∧
        HeadDiv w D S zero mul A a j ∧ Divides W G y j ∧ Divides WN GN J q := by
  intro a fa y Y q hfa hY hq haq hyq
  have hbD := function_input hf.1.1.1 hb
  have hfbN := hf.1.1.2 b fb hb
  have hyW := function_input hH.1 hY
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hbD hUnit hG
  by_cases hay : HeadDiv w D S zero mul A a y
  · exact ⟨y,Y,hyW,hY,hay,⟨unit,hmW.1.1,((hmW.1.2 y hyW y).2).mpr rfl⟩,hyq⟩
  have hPair := transport_old_pair_below hM hw hz hzw hm hmN hAlpha hAlphaN hf hb hW hWN
    hG hGN hH hGraph hO hON hJ hA hC
  rcases cases_raw hM hw hz hzw (word_raw hW hyW) with ⟨c,hc⟩ | ⟨s,t,hCons⟩
  · obtain ⟨fc,hfc,_⟩ := hf.1.1.1.2 c hc.1
    have hOldN := ConstructionProbeRawTransport.transport_old hM hz hf.1.1 hc hfc ((hGraph y Y).mp hY).2
    have hcq := (old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN hOldN hq).mp hyq
    obtain ⟨j,J,hj,hJmap,haj,hcj,hJq⟩ := hPair a c fa fc q hfa hfc hq haq hcq
    exact ⟨j,J,hj,hJmap,haj,(old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hbD hG hc hj).mpr hcj,hJq⟩
  · obtain ⟨gs,hgs,_⟩ := hAlphabet.1.1.1.2 s (cons_letter hCons)
    have hhead : HeadSome w D S y s := ⟨t,hCons⟩
    have hheadN := (ConstructionProbeHeadTransport.head_transport_some hM hw hz hzw hf.1.1 hAlphabet.1
      ((hGraph y Y).mp hY).2 hgs).mpr hhead
    have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hf.1 hPres hf.2.1
    have hExit : ¬ HeadSome w N SN q gs := fun hqhead => hay
      ((ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1 hDiv hAlphabet.2.2.2 hfa
        ((hGraph y Y).mp hY).2).mp ((headDiv_of_same_head hM hw hz hheadN hqhead).mpr haq))
    obtain ⟨k,fk,_,hfk,hgate,hgateN⟩ := ConstructionProbeSharedGates.exists_simulated_gate_of_exit hM hw hz hzw
      hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC
      y (word_raw hW hyW) Y s gs q hY hgs hhead hq hyq hExit
    obtain ⟨j,J,hj,hJmap,haj,hkj,hJq⟩ := hPair a k fa fk q hfa hfk hq haq ((hgateN q hq).mp ⟨hyq,hExit⟩)
    exact ⟨j,J,hj,hJmap,haj,((hgate j hj).mpr hkj).1,hJq⟩

theorem transport_dvd_of_different_head (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hH : MapsTo W WN H) (hGraph : WordGraph w D S SN f g W H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∀ x y X Y s t gs gt q, PureKuratowski.PairMember M x X H → PureKuratowski.PairMember M y Y H →
      PureKuratowski.PairMember M s gs g → PureKuratowski.PairMember M t gt g →
      HeadSome w D S x s → HeadSome w D S y t → s ≠ t →
      (Project.FirstOrderSemantics.reduct M).mem q WN → Divides WN GN Y q → HeadSome w N SN q gs → Divides W G y x := by
  intro x y X Y s t gs gt q hX hY hgs hgt hxhead hyhead hst hq hyq hqhead
  have hxW := function_input hH.1 hX
  have hyW := function_input hH.1 hY
  have hExit : ¬ HeadSome w N SN q gt := by
    intro hqt
    have he := head_unique hM hw hqhead hqt
    subst gt
    exact hst (hAlphabet.1.2 s t gs hgs hgt)
  obtain ⟨k,fk,_,hfk,hgate,hgateN⟩ := ConstructionProbeSharedGates.exists_simulated_gate_of_exit hM hw hz hzw
    hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC
    y (word_raw hW hyW) Y t gt q hY hgt hyhead hq hyq hExit
  have hxheadN := (ConstructionProbeHeadTransport.head_transport_some hM hw hz hzw hf.1.1 hAlphabet.1
    ((hGraph x X).mp hX).2 hgs).mpr hxhead
  have hkX := (headDiv_of_same_head hM hw hz hxheadN hqhead).mpr ((hgateN q hq).mp ⟨hyq,hExit⟩)
  have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hf.1 hPres hf.2.1
  have hkx := (ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1 hDiv hAlphabet.2.2.2 hfk
    ((hGraph x X).mp hX).2).mp hkX
  exact ((hgate x hxW).mpr hkx).1

def CommonAt (W WN G GN H x : M.Carrier .set) : Prop := ∀ y X Y q,
  PureKuratowski.PairMember M x X H → PureKuratowski.PairMember M y Y H →
  (Project.FirstOrderSemantics.reduct M).mem q WN → Divides WN GN X q → Divides WN GN Y q →
    ∃ j J, (Project.FirstOrderSemantics.reduct M).mem j W ∧ PureKuratowski.PairMember M j J H ∧
      Divides W G x j ∧ Divides W G y j ∧ Divides WN GN J q

def commonAt {m : Nat} (W WN G GN H x : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ x.succ.succ.succ.succ 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ 3 1)) (.imp (.mem (.bound 0) (.bound WN.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ GN.succ.succ.succ.succ 2 0))
  (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ GN.succ.succ.succ.succ
  1 0)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound W.succ.succ.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 1 0)) (.conj
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ x.succ.succ.succ.succ.succ.succ 1)) (.conj (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ 5 1))
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ 0 2)))))))))))))))))

theorem commonAt_freeClosed {m : Nat} (W WN G GN H x : Fin m) : (commonAt W WN G GN H x).FreeClosed := by
  simp -implicitDefEqProofs [commonAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem commonAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W WN G GN H x : Fin m) :
    Project.Formula.satisfies env (commonAt W WN G GN H x) ↔
      CommonAt (env.bound W) (env.bound WN) (env.bound G) (env.bound GN) (env.bound H) (env.bound x) := by
  simp only [commonAt,CommonAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

theorem transport_common_below (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hH : MapsTo W WN H) (hGraph : WordGraph w D S SN f g W H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∀ x, Raw w D S x → CommonAt W WN G GN H x := by
  have hbD := function_input hf.1.1.1 hb
  have hfbN := hf.1.1.2 b fb hb
  have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hf.1 hPres hf.2.1
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hbD hUnit hG
  have hOld := transport_old_common_below hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN
    hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC
  have hPair := transport_old_pair_below hM hw hz hzw hm hmN hAlpha hAlphaN hf hb hW hWN
    hG hGN hH hGraph hO hON hJ hA hC
  have hDifferent := transport_dvd_of_different_head hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN
    hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC
  have hGate := ConstructionProbeSharedGates.exists_simulated_gate_of_exit hM hw hz hzw hm hmN hAlpha hAlphaN
    hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC
  have hCtor : ConstructionProbeRawTransport.ConstructorLaws w D N S SN zero f g H :=
    ⟨fun _ _ _ _ ha hx hX => ConstructionProbeRawTransport.transport_old hM hz hf.1.1 hx ha ((hGraph _ _).mp hX).2,
      fun _ _ _ _ _ _ hs hc ht hx => ConstructionProbeRawTransport.transport_cons hM hw hf.1.1 hAlphabet.1.1 hc hs
        ((hGraph _ _).mp ht).2 ((hGraph _ _).mp hx).2⟩
  have hSim : ConstructionProbeRawTransport.SimulationLaws w D N S SN zero mul mulN A AN f H :=
    ⟨fun _ _ _ _ ha hx => ⟨ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1 hDiv
        hAlphabet.2.2.2 ha ((hGraph _ _).mp hx).2,
      ConstructionProbeRawTransport.reduced_transport hM hw hf.1.1 hAlphabet.1.1 hDiv hAlphabet.2.2.2 ha ((hGraph _ _).mp hx).2⟩,
      fun _ _ _ _ _ _ ha hx hy hact => ConstructionProbeRawTransport.transport_oldAct hM hw hz hf.1.1 hAlphabet.1.1
        hPres hAlphabet.2.1 ha ((hGraph _ _).mp hx).2 ((hGraph _ _).mp hy).2 hact⟩
  have hRed := ConstructionProbeTransportHom.reduction_laws hf.1.1 hAlphabet.1.1 hH hAlpha.2.2.2.1 hCtor hSim hAlphabet.2.2.1 hb
  let schema : Project.UnarySchema 5 := {
    body := commonAt 1 2 3 4 5 0
    freeClosed := commonAt_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases W (Fin.cases WN (Fin.cases G (Fin.cases GN (fun _ => H)))), free := fun _ => w }
  have he (x) : schema.denote env x ↔ CommonAt W WN G GN H x := commonAt_semantics hM (env.push x) 1 2 3 4 5 0
  have hAll : ∀ x, Raw w D S x → schema.denote env x := by
    apply ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw
    · intro a x ha
      apply (he x).mpr
      intro y X Y q hX hY hq hxq hyq
      obtain ⟨fa,hfa,_⟩ := hf.1.1.1.2 a ha.1
      have haN := hCtor.1 a fa x X hfa ha hX
      obtain ⟨j,J,hj,hJmap,haj,hyj,hJq⟩ := hOld a fa y Y q hfa hY hq
        ((old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN haN hq).mp hxq) hyq
      exact ⟨j,J,hj,hJmap,(old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hbD hG ha hj).mpr haj,hyj,hJq⟩
    · intro s t x hCons ih
      apply (he x).mpr
      intro y X Y q hX hY hq hxq hyq
      have hxW := function_input hH.1 hX
      have hyW := function_input hH.1 hY
      have htW := (hW t).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW x).mp hxW)).1
      obtain ⟨T,hT,_⟩ := hH.1.2 t htW
      obtain ⟨gs,hgs,_⟩ := hAlphabet.1.1.1.2 s (cons_letter hCons)
      have hConsN := hCtor.2 s gs t T x X hgs hCons hT hX
      rcases cases_raw hM hw hz hzw (word_raw hW hyW) with ⟨a,ha⟩ | ⟨r,u,hConsY⟩
      · obtain ⟨fa,hfa,_⟩ := hf.1.1.1.2 a ha.1
        have haN := hCtor.1 a fa y Y hfa ha hY
        obtain ⟨j,J,hj,hJmap,haj,hxj,hJq⟩ := hOld a fa x X q hfa hX hq
          ((old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN haN hq).mp hyq) hxq
        exact ⟨j,J,hj,hJmap,hxj,(old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hbD hG ha hj).mpr haj,hJq⟩
      · by_cases hsr : s = r
        · subst r
          have huW := (hW u).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hConsY).mp ((hW y).mp hyW)).1
          obtain ⟨U,hU,_⟩ := hH.1.2 u huW
          have hConsYN := hCtor.2 s gs u U y Y hgs hConsY hU hY
          obtain ⟨v,hv,hXv⟩ := hxq
          obtain ⟨v',hv',hYv⟩ := hyq
          obtain ⟨Tv,hTv,hLetter⟩ := (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hmN hAlphaN hWN hfbN hConsN).mp ((hGN X v q).mp hXv).2
          obtain ⟨Uv,hUv,hLetter'⟩ := (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hmN hAlphaN hWN hfbN hConsYN).mp ((hGN Y v' q).mp hYv).2
          have hTU := ConstructionProbeLetterAction.letterAct_injective hM hw hz hzw hmN hAlphaN hLetter hLetter'
          subst Uv
          obtain ⟨j,J,hj,hJmap,htj,huj,hJTv⟩ := (he t).mp ih u T U Tv hT hU (ConstructionProbeEvaluation.eval_word hM hTv)
            ⟨v,hv,(hGN T v Tv).mpr ⟨hH.2 t T hT,hTv⟩⟩ ⟨v',hv',(hGN U v' Tv).mpr ⟨hH.2 u U hU,hUv⟩⟩
          obtain ⟨out,hout⟩ := ConstructionProbeLetterAction.letterAct_total hM hw hz hzw hm hAlpha hW hbD (cons_letter hCons) hj
          have houtW := ConstructionProbeLetterAction.letterAct_word hM hw hz hzw hW hout
          obtain ⟨Out,hOut,_⟩ := hH.1.2 out houtW
          have houtN := hRed.2 s gs j J out Out hgs hJmap hOut hout
          refine ⟨out,Out,houtW,hOut,?_,?_,?_⟩
          · obtain ⟨v,hv,hp⟩ := htj
            exact ⟨v,hv,(hG x v out).mpr ⟨hxW,(ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hm hAlpha hW hbD hCons).mpr
              ⟨j,((hG t v j).mp hp).2,hout⟩⟩⟩
          · obtain ⟨v,hv,hp⟩ := huj
            exact ⟨v,hv,(hG y v out).mpr ⟨hyW,(ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hm hAlpha hW hbD hConsY).mpr
              ⟨j,((hG u v j).mp hp).2,hout⟩⟩⟩
          · obtain ⟨v,hv,hp⟩ := hJTv
            exact ⟨v,hv,(hGN Out v q).mpr ⟨hH.2 out Out hOut,
              ConstructionProbeEvaluationLaws.eval_letterAct hM hw hz hzw hmN hAlphaN hWN hfbN houtN ((hGN J v Tv).mp hp).2 hLetter⟩⟩
        · obtain ⟨gr,hgr,_⟩ := hAlphabet.1.1.1.2 r (cons_letter hConsY)
          by_cases hqs : HeadSome w N SN q gs
          · exact ⟨x,X,hxW,hX,⟨unit,hmW.1.1,((hmW.1.2 x hxW x).2).mpr rfl⟩,
              hDifferent x y X Y s r gs gr q hX hY hgs hgr ⟨t,hCons⟩ ⟨u,hConsY⟩ hsr hq hyq hqs,hxq⟩
          · by_cases hqr : HeadSome w N SN q gr
            · exact ⟨y,Y,hyW,hY,hDifferent y x Y X r s gr gs q hY hX hgr hgs ⟨u,hConsY⟩ ⟨t,hCons⟩ (Ne.symm hsr) hq hxq hqr,
                ⟨unit,hmW.1.1,((hmW.1.2 y hyW y).2).mpr rfl⟩,hyq⟩
            · obtain ⟨k,fk,_,hfk,hgate,hgateN⟩ := hGate x (word_raw hW hxW) X s gs q hX hgs ⟨t,hCons⟩ hq hxq hqs
              obtain ⟨l,fl,_,hfl,hgate',hgateN'⟩ := hGate y (word_raw hW hyW) Y r gr q hY hgr ⟨u,hConsY⟩ hq hyq hqr
              obtain ⟨j,J,hj,hJmap,hkj,hlj,hJq⟩ := hPair k l fk fl q hfk hfl hq ((hgateN q hq).mp ⟨hxq,hqs⟩) ((hgateN' q hq).mp ⟨hyq,hqr⟩)
              exact ⟨j,J,hj,hJmap,((hgate j hj).mpr hkj).1,((hgate' j hj).mpr hlj).1,hJq⟩
  exact fun x hx => (he x).mp (hAll x hx)

open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics)
open ConstructionProbeConservativeSyntax (conservative conservative_freeClosed conservative_semantics)
open ConstructionProbeOldEmbeddingSyntax (oldGraph oldGraph_freeClosed oldGraph_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordTransport (wordGraph wordGraph_freeClosed wordGraph_semantics)
open ConstructionProbeSharedIntersections (conditionalJoins conditionalJoins_freeClosed conditionalJoins_semantics)

def commonSentence : Project.Sentence where
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
    (2 : Fin 29) (20 : Fin 29) (26 : Fin 29)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 :
    Fin 29) (15 : Fin 29) (16 : Fin 29))) (.imp (wordGraph (0 : Fin 29) (1 : Fin 29) (3 : Fin 29) (4 : Fin 29)
    (12 : Fin 29) (13 : Fin 29) (15 : Fin 29) (14 : Fin 29)) (.imp (oldGraph (5 : Fin 29) (1 : Fin 29) (27 :
    Fin 29)) (.imp (oldGraph (5 : Fin 29) (2 : Fin 29) (28 : Fin 29)) (.imp (conditionalJoins (1 : Fin 29) (6
    : Fin 29)) (.imp (conservative (1 : Fin 29) (15 : Fin 29) (6 : Fin 29) (23 : Fin 29) (27 : Fin 29)) (.imp
    (conservative (2 : Fin 29) (16 : Fin 29) (7 : Fin 29) (24 : Fin 29) (28 : Fin 29)) (.forallE (.imp (raw (0
    : Fin 29).succ (1 : Fin 29).succ (3 : Fin 29).succ 0) (commonAt (15 : Fin 29).succ (16 : Fin 29).succ (23 : Fin 29).succ (24 : Fin 29).succ (14 : Fin 29).succ 0)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,alphabetSimulation_freeClosed,conservative_freeClosed,preservesProducts_freeClosed,
      wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,wordGraph_freeClosed,oldGraph_freeClosed,
      conditionalJoins_freeClosed,raw_freeClosed,commonAt_freeClosed]

theorem common_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence commonSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) commonSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    alphabet_semantics hM,alphabetSimulation_semantics hM,conservative_semantics hM,preservesProducts_semantics hM,
    wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,wordGraph_semantics hM,
    oldGraph_semantics hM,conditionalJoins_semantics hM,raw_semantics hM,commonAt_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC =>
    transport_common_below hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC

theorem common_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence commonSentence) := ModelTransfer.derives (fun _ hM => common_models hM)

end PPAC.Migration.ConstructionProbeTransportCommon
