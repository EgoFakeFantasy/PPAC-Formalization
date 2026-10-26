/- Pinned ProbePresentations.Word.exists_simulated_gate_of_exit (284-348).
The source Raw induction uses the existing pure-formula raw_induction, with
all varying heads and target words quantified inside its schema. -/
import PPAC.Migration.ConstructionProbeHeadTransport
import PPAC.Migration.ConstructionProbeSharedIntersections
import PPAC.Migration.ConstructionProbeTransportHom

namespace PPAC.Migration.ConstructionProbeSharedGates
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

def SharedGateAt (w D N S SN zero mul mulN A AN W WN G GN f g H x : M.Carrier .set) : Prop :=
  ∀ X s gs q, PureKuratowski.PairMember M x X H → PureKuratowski.PairMember M s gs g →
    HeadSome w D S x s → (Project.FirstOrderSemantics.reduct M).mem q WN →
    Divides WN GN X q → ¬ HeadSome w N SN q gs →
      ∃ j fj, (Project.FirstOrderSemantics.reduct M).mem j D ∧ PureKuratowski.PairMember M j fj f ∧
        Gate w D S zero mul A W G x s j ∧ Gate w N SN zero mulN AN WN GN X gs fj

def sharedGateAt {m : Nat} (w D N S SN zero mul mulN A AN W WN G GN f g H x : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ x.succ.succ.succ.succ 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ 2 1)) (.imp (headSome w.succ.succ.succ.succ D.succ.succ.succ.succ
  S.succ.succ.succ.succ x.succ.succ.succ.succ 2) (.imp (.mem (.bound 0) (.bound WN.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ GN.succ.succ.succ.succ 3 0))
  (.imp (.neg (headSome w.succ.succ.succ.succ N.succ.succ.succ.succ SN.succ.succ.succ.succ 0 1)) (.existsE
  (.existsE (.conj (.mem (.bound 1) (.bound D.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 1 0)) (.conj (gate w.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ x.succ.succ.succ.succ.succ.succ 4 1) (gate w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ SN.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ AN.succ.succ.succ.succ.succ.succ WN.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ 5 3 0))))))))))))))))

theorem sharedGateAt_freeClosed {m : Nat} (w D N S SN zero mul mulN A AN W WN G GN f g H x : Fin m) :
    (sharedGateAt w D N S SN zero mul mulN A AN W WN G GN f g H x).FreeClosed := by
  simp -implicitDefEqProofs [sharedGateAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    headSome_freeClosed,gate_freeClosed]

theorem sharedGateAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D N S SN zero mul mulN A AN W WN G GN f g H x : Fin m) :
    Project.Formula.satisfies env (sharedGateAt w D N S SN zero mul mulN A AN W WN G GN f g H x) ↔
      SharedGateAt (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN) (env.bound zero)
        (env.bound mul) (env.bound mulN) (env.bound A) (env.bound AN) (env.bound W) (env.bound WN)
        (env.bound G) (env.bound GN) (env.bound f) (env.bound g) (env.bound H) (env.bound x) := by
  simp only [sharedGateAt,SharedGateAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),headSome_semantics hM,gate_semantics hM]
  rfl

/-- One base witness supplies both old intersections, now in the source HeadDiv form. -/
theorem shared_headDiv_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb W WN E EN e eN I IN G GN f O ON x y fx fy z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hfb : (Project.FirstOrderSemantics.reduct M).mem fb N)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hf : Conservative D N mul mulN f)
    (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z WN)
    (hxz : HeadDiv w N SN zero mulN AN fx z) (hyz : HeadDiv w N SN zero mulN AN fy z) :
    ∃ j fj, (Project.FirstOrderSemantics.reduct M).mem j D ∧ PureKuratowski.PairMember M j fj f ∧
      (∀ v, (Project.FirstOrderSemantics.reduct M).mem v W →
        ((HeadDiv w D S zero mul A x v ∧ HeadDiv w D S zero mul A y v) ↔ HeadDiv w D S zero mul A j v)) ∧
      (∀ v, (Project.FirstOrderSemantics.reduct M).mem v WN →
        ((HeadDiv w N SN zero mulN AN fx v ∧ HeadDiv w N SN zero mulN AN fy v) ↔ HeadDiv w N SN zero mulN AN fj v)) := by
  obtain ⟨ox,hox,_⟩ := hA.1.1.1.2 x (function_input hf.1.1.1 hfx)
  obtain ⟨oy,hoy,_⟩ := hA.1.1.1.2 y (function_input hf.1.1.1 hfy)
  obtain ⟨Ox,hOx,_⟩ := hC.1.1.1.2 fx (hf.1.1.2 x fx hfx)
  obtain ⟨Oy,hOy,_⟩ := hC.1.1.1.2 fy (hf.1.1.2 y fy hfy)
  have sourceDiv (a oa v) (ha : PureKuratowski.PairMember M a oa O)
      (hv : (Project.FirstOrderSemantics.reduct M).mem v W) :=
    old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ((hO a oa).mp ha) hv
  have targetDiv (a oa v) (ha : PureKuratowski.PairMember M a oa ON)
      (hv : (Project.FirstOrderSemantics.reduct M).mem v WN) :=
    old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfb hGN ((hON a oa).mp ha) hv
  obtain ⟨j,fj,oj,Oj,hj,hfj,hoj,hOj,hjoin,hjoinN⟩ :=
    shared_intersections hJ hf hA hC x y fx fy ox oy Ox Oy z hfx hfy hox hoy hOx hOy hzW
      ((targetDiv fx Ox z hOx hzW).mpr hxz) ((targetDiv fy Oy z hOy hzW).mpr hyz)
  refine ⟨j,fj,hj,hfj,?_,?_⟩
  · intro v hv
    exact ((and_congr (sourceDiv x ox v hox hv).symm (sourceDiv y oy v hoy hv).symm).trans
      (hjoin v hv)).trans (sourceDiv j oj v hoj hv)
  · intro v hv
    exact ((and_congr (targetDiv fx Ox v hOx hv).symm (targetDiv fy Oy v hOy hv).symm).trans
      (hjoinN v hv)).trans (targetDiv fj Oj v hOj hv)

/-- Literal shared-gate recursion; no gate-existence premise or external Raw induction. -/
theorem exists_simulated_gate_of_exit (hM : FirstOrder.Theory.Models M nativeZF)
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
    ∀ x, Raw w D S x → SharedGateAt w D N S SN zero mul mulN A AN W WN G GN f g H x := by
  have hbD := function_input hf.1.1.1 hb
  have hfbN := hf.1.1.2 b fb hb
  have hDiv := ConstructionProbeAlphabetMap.division_reflection hm hmN hf.1 hPres hf.2.1
  have hShared {x y fx fy z : M.Carrier .set} := shared_headDiv_intersection hM (x := x) (y := y) (fx := fx) (fy := fy) (z := z) hw hz hzw hm hmN hAlpha hAlphaN hW hWN hbD hfbN hG hGN hO hON hJ hf hA hC
  let schema : Project.UnarySchema 17 := {
    body := sharedGateAt 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 0
    freeClosed := sharedGateAt_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 17 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases N (Fin.cases S (Fin.cases SN (Fin.cases zero (Fin.cases mul (Fin.cases mulN (Fin.cases A (Fin.cases AN (Fin.cases W (Fin.cases WN (Fin.cases G (Fin.cases GN (Fin.cases f (Fin.cases g (fun _ => H)))))))))))))))),
      free := fun _ => w }
  have he (x) : schema.denote env x ↔ SharedGateAt w D N S SN zero mul mulN A AN W WN G GN f g H x :=
    sharedGateAt_semantics hM (env.push x) 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 0
  have hAll : ∀ x, Raw w D S x → schema.denote env x := by
    apply ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw
    · intro y x hx
      apply (he x).mpr
      intro X s gs q _ _ hhead
      exact (old_no_head hz hx hhead).elim
    · intro t Y x hCons ih
      apply (he x).mpr
      intro X s gs q hX hgs hhead hq hxq hqhead
      have hts : t = s := head_unique hM hw ⟨Y,hCons⟩ hhead
      subst t
      have hred := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp
        ((hW x).mp (function_input hH.1 hX))
      have hY := (hW Y).mpr hred.1
      obtain ⟨T,hT,_⟩ := hH.1.2 Y hY
      have hTN := hH.2 Y T hT
      have hConsN := ConstructionProbeRawTransport.transport_cons hM hw hf.1.1 hAlphabet.1.1
        hCons hgs ((hGraph Y T).mp hT).2 ((hGraph x X).mp hX).2
      have hnotN : ¬ HeadDiv w N SN zero mulN AN fb T := fun h => hred.2
        ((ConstructionProbeRawTransport.headDiv_transport hM hw hz hzw hf.1.1 hAlphabet.1.1
          hDiv hAlphabet.2.2.2 hb ((hGraph Y T).mp hT).2).mp h)
      obtain ⟨v,hv,hprod⟩ := hxq
      obtain ⟨Tv,hTv,hletter⟩ := (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hmN hAlphaN hWN hfbN hConsN).mp
        ((hGN X v q).mp hprod).2
      have hTvN := ConstructionProbeEvaluation.eval_word hM hTv
      have hTdiv : Divides WN GN T Tv := ⟨v,hv,(hGN T v Tv).mpr ⟨hTN,hTv⟩⟩
      have hfbTv := (head_letterAct_ne_iff hM hw hz hzw hAlphaN hletter).mp hqhead
      have hInt : ∃ j fj, (Project.FirstOrderSemantics.reduct M).mem j D ∧ PureKuratowski.PairMember M j fj f ∧
          (∀ z, (Project.FirstOrderSemantics.reduct M).mem z W →
            ((Divides W G Y z ∧ HeadDiv w D S zero mul A b z) ↔ HeadDiv w D S zero mul A j z)) ∧
          (∀ z, (Project.FirstOrderSemantics.reduct M).mem z WN →
            ((Divides WN GN T z ∧ HeadDiv w N SN zero mulN AN fb z) ↔ HeadDiv w N SN zero mulN AN fj z)) := by
        rcases cases_raw hM hw hz hzw (word_raw hW hY) with ⟨y,hy⟩ | ⟨t,Z,ht⟩
        · obtain ⟨fy,hfy,_⟩ := hf.1.1.1.2 y hy.1
          have hOldN := ConstructionProbeRawTransport.transport_old hM hz hf.1.1 hy hfy ((hGraph Y T).mp hT).2
          obtain ⟨j,fj,hj,hfj,hjoin,hjoinN⟩ := hShared hfy hb hTvN
            ((old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN hOldN hTvN).mp hTdiv) hfbTv
          refine ⟨j,fj,hj,hfj,?_,?_⟩
          · intro z hzW
            exact (and_congr (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hbD hG hy hzW) Iff.rfl).trans (hjoin z hzW)
          · intro z hzWN
            exact (and_congr (old_dvd_iff_headDiv hM hw hz hzw hmN hAlphaN hWN hfbN hGN hOldN hzWN) Iff.rfl).trans (hjoinN z hzWN)
        · obtain ⟨gt,hgt,_⟩ := hAlphabet.1.1.1.2 t (cons_letter ht)
          have hYhead : HeadSome w D S Y t := ⟨Z,ht⟩
          have hThead := (ConstructionProbeHeadTransport.head_transport_some hM hw hz hzw hf.1.1 hAlphabet.1
            ((hGraph Y T).mp hT).2 hgt).mpr hYhead
          have hExit : ¬ HeadSome w N SN Tv gt := fun hh =>
            hnotN ((headDiv_of_same_head hM hw hz hThead hh).mpr hfbTv)
          obtain ⟨k,fk,hk,hfk,hgate,hgateN⟩ := (he Y).mp ih T t gt Tv hT hgt hYhead hTvN hTdiv hExit
          obtain ⟨j,fj,hj,hfj,hjoin,hjoinN⟩ := hShared hfk hb hTvN ((hgateN Tv hTvN).mp ⟨hTdiv,hExit⟩) hfbTv
          refine ⟨j,fj,hj,hfj,?_,?_⟩
          · intro z hzW
            exact (and_comm.trans (gate_old_intersection hM hw hz hgate hYhead hred.2 hzW)).trans
              (and_comm.trans (hjoin z hzW))
          · intro z hzWN
            exact (and_comm.trans (gate_old_intersection hM hw hz hgateN hThead hnotN hzWN)).trans
              (and_comm.trans (hjoinN z hzWN))
      obtain ⟨j,fj,hj,hfj,hint,hintN⟩ := hInt
      obtain ⟨oj,hoj⟩ := exists_old hM (zero := zero) hj
      have hojW := old_word hM hz hzw hW hoj
      have hjj : HeadDiv w D S zero mul A j oj :=
        (headDiv_old_iff hz hoj).mpr ⟨e,hm.1.1,((hm.1.2 j hj j).2).mpr rfl⟩
      obtain ⟨u,hu,hbu⟩ := (headDiv_old_iff hz hoj).mp (((hint oj hojW).mpr hjj).2)
      obtain ⟨ex,hex,_⟩ := hAlpha.2.2.2.1.1.2 s (cons_letter hCons)
      have hexD := hAlpha.2.2.2.1.2 s ex hex
      obtain ⟨jout,hjout,hprodout⟩ := (hm.2.1 ex hexD).1 u hu
      obtain ⟨fu,hfu,_⟩ := hf.1.1.1.2 u hu
      obtain ⟨fex,hfex,_⟩ := hf.1.1.1.2 ex hexD
      obtain ⟨fjout,hfjout,_⟩ := hf.1.1.1.2 jout hjout
      exact ⟨jout,fjout,hjout,hfjout,
        gate_of_suffix_intersection hM hw hz hzw hm hAlpha hW hbD hG hUnit hCons hY hred.2 hu hbu hex hprodout hint,
        gate_of_suffix_intersection hM hw hz hzw hmN hAlphaN hWN hfbN hGN hUnitN hConsN hTN hnotN
          (hf.1.1.2 u fu hfu) (hPres b u j fb fu fj hbu hb hfu hfj)
          (hAlphabet.2.2.1 s ex gs fex hex hgs hfex) (hPres ex u jout fex fu fjout hprodout hfex hfu hfjout) hintN⟩
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

def sharedSentence : Project.Sentence where
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
    : Fin 29).succ (1 : Fin 29).succ (3 : Fin 29).succ 0) (sharedGateAt (0 : Fin 29).succ (1 : Fin 29).succ (2
    : Fin 29).succ (3 : Fin 29).succ (4 : Fin 29).succ (5 : Fin 29).succ (6 : Fin 29).succ (7 : Fin 29).succ
    (8 : Fin 29).succ (9 : Fin 29).succ (15 : Fin 29).succ (16 : Fin 29).succ (23 : Fin 29).succ (24 : Fin
    29).succ (12 : Fin 29).succ (13 : Fin 29).succ (14 : Fin 29).succ 0)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,alphabetSimulation_freeClosed,conservative_freeClosed,preservesProducts_freeClosed,
      wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,wordGraph_freeClosed,oldGraph_freeClosed,
      conditionalJoins_freeClosed,raw_freeClosed,sharedGateAt_freeClosed]

theorem shared_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence sharedSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) sharedSentence]
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
    oldGraph_semantics hM,conditionalJoins_semantics hM,raw_semantics hM,sharedGateAt_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC =>
    exists_simulated_gate_of_exit hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hO hON hJ hA hC

theorem shared_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence sharedSentence) := ModelTransfer.derives (fun _ hM => shared_models hM)

end PPAC.Migration.ConstructionProbeSharedGates
