/- Pinned PersistentCodes.ordF_eq_check_le:521-584.
The source Child induction and least missing ordinal are instantiated with
existing internal formula induction and ObjectOrdinalLeast. All names and
ordinals range over the same arbitrary native ZF model. -/
import PPAC.Migration.ForcingCheckReflection
import PPAC.Migration.ForcingRawRank
import PPAC.Migration.ForcingOrdinalTransitivity

namespace PPAC.Migration.ForcingOrdinalDecision
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Ordinal Rank ordinal_semantics rank_semantics)
open ForcingClassEvaluation (Predicate)
open ForcingOrdinalTransitivity (OrdF ordF)
open ForcingHS (HS)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem ordinal_irrefl (hM : FirstOrder.Theory.Models M nativeZF) {a : M.Carrier .set}
    (ha : Ordinal a) : ¬(Project.FirstOrderSemantics.reduct M).mem a a := by
  have h := ForcingRawRank.closed_truth hM ((OrdinalSyntax.ordinal (0 : Fin 1)).imp
    (Formula.mem 0 0).neg) ObjectOrdinalBasic.native_noSelf (Source.SetLanguage.args1 a)
  exact h ha

theorem ordinal_compare (hM : FirstOrder.Theory.Models M nativeZF) {a b : M.Carrier .set}
    (ha : Ordinal a) (hb : Ordinal b) : a = b ∨
      (Project.FirstOrderSemantics.reduct M).mem a b ∨ (Project.FirstOrderSemantics.reduct M).mem b a := by
  have h := ForcingRawRank.closed_truth hM ((OrdinalSyntax.ordinal (0 : Fin 2)).imp
    ((OrdinalSyntax.ordinal 1).imp (OrdinalComparison.comparison 0 1)))
    ObjectOrdinalComparison.native_comparison (Source.SetLanguage.args2 a b)
  simp only [Formula.Realize,ordinal_semantics (M := M),OrdinalComparison.comparison,Formula.Realize] at h
  exact h ha hb

def missing {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top sigma p a : Fin m) : Formula m := .all
  ((checkName top.castSucc a.castSucc (Fin.last m)).imp
    (forces false L (paramsUp lp) P.castSucc (Fin.last m) sigma.castSucc p.castSucc).neg)

theorem missing_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top sigma p a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (missing L lp P top sigma p a) ↔
      ∀ na, Checked (env top) (env a) na → ¬Forces false L (fun i => env (lp i)) (env P) na (env sigma) (env p) := by
  simp only [missing,Formula.Realize,Source.Formula.neg,Formula.Realize,
    ForcingCheckName.checkName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem least_missing (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (L : Formula (k+2)) (lp : Fin k → M.Carrier .set) (P top sigma p a : M.Carrier .set)
    (ha : Ordinal a) (hm : ∀ na, Checked top a na → ¬Forces false L lp P na sigma p) :
    ∃ b, Ordinal b ∧ (∀ nb, Checked top b nb → ¬Forces false L lp P nb sigma p) ∧
      ∀ c, Ordinal c → (∀ nc, Checked top c nc → ¬Forces false L lp P nc sigma p) →
        b = c ∨ (Project.FirstOrderSemantics.reduct M).mem b c := by
  let inputs : Fin (k+4) → M.Carrier .set := Fin.lastCases p (Fin.lastCases sigma (Fin.lastCases top (Fin.lastCases P lp)))
  let matrix := missing L (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
    (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hm' : ∀ b, Predicate matrix inputs b ↔
      ∀ nb, Checked top b nb → ¬Forces false L lp P nb sigma p := by
    intro b
    unfold Predicate
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      missing_semantics (M := M) (Fin.lastCases b inputs) L
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
        (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have h := ForcingRawRank.closed_truth hM
    ((OrdinalLeastSyntax.has matrix id).imp (OrdinalLeastSyntax.leastExists matrix id))
    (ObjectOrdinalLeast.native_existence matrix) inputs
  simp only [OrdinalLeastSyntax.has,OrdinalLeastSyntax.leastExists,OrdinalLeastSyntax.least,
    OrdinalLeastSyntax.property,Formula.Realize,ordinal_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] at h
  obtain ⟨b,⟨hb,hmb⟩,hmin⟩ := h ⟨a,ha,(hm' a).mpr hm⟩
  exact ⟨b,hb,(hm' b).mp hmb,fun c hc hmc => hmin c ⟨hc,(hm' c).mpr hmc⟩⟩

def Decision {k : Nat} (L : Formula (k+2)) (lp : Fin k → M.Carrier .set)
    (P top sigma p a : M.Carrier .set) : Prop :=
  ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel L lp q p ∧
    ∃ b, Ordinal b ∧ (b = a ∨ (Project.FirstOrderSemantics.reduct M).mem b a) ∧
      ∃ nb, Checked top b nb ∧ Forces true L lp P sigma nb q

def decision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top sigma p a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let q := (Fin.last m).castSucc.castSucc
  let b := (Fin.last (m+1)).castSucc
  let nb := Fin.last (m+2)
  .ex (.ex (.ex ((Formula.mem q (up P)).conj ((rel L (fun i => up (lp i)) q (up p)).conj
    ((OrdinalSyntax.ordinal b).conj (((Formula.equal b (up a)).disj (.mem b (up a))).conj
      ((checkName (up top) b nb).conj (forces true L (fun i => up (lp i)) (up P) (up sigma) nb q))))))))

theorem decision_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top sigma p a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (decision L lp P top sigma p a) ↔
      Decision L (fun i => env (lp i)) (env P) (env top) (env sigma) (env p) (env a) := by
  simp only [decision,Decision,Formula.Realize,ordinal_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · rintro ⟨q,b,nb,hq,hqp,hb,hba,hn,he⟩
    exact ⟨q,hq,hqp,b,hb,hba,nb,hn,he⟩
  · rintro ⟨q,hq,hqp,b,hb,hba,nb,hn,he⟩
    exact ⟨q,b,nb,hq,hqp,hb,hba,hn,he⟩

def inductionAt {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → Fin m) (P top sigma : Fin m) : Formula m :=
  (MinimalPredicates.pred H lp sigma).imp (.all (.all
    ((Formula.mem (Fin.last m).castSucc P.castSucc.castSucc).imp
      ((LayerRankSyntax.rank sigma.castSucc.castSucc (Fin.last (m+1))).imp
        ((ordF L H (paramsUp (paramsUp lp)) P.castSucc.castSucc (Fin.last m).castSucc sigma.castSucc.castSucc).imp
          (decision L (paramsUp (paramsUp lp)) P.castSucc.castSucc top.castSucc.castSucc sigma.castSucc.castSucc
            (Fin.last m).castSucc (Fin.last (m+1))))))))

theorem inductionAt_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m) (P top sigma : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (inductionAt L H lp P top sigma) ↔
      (Predicate H (fun i => env (lp i)) (env sigma) → ∀ p a,
        (Project.FirstOrderSemantics.reduct M).mem p (env P) → Rank (env sigma) a →
        OrdF L H (fun i => env (lp i)) (env P) p (env sigma) →
        Decision L (fun i => env (lp i)) (env P) (env top) (env sigma) p a) := by
  simp only [inductionAt,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    rank_semantics (M := M),ForcingOrdinalTransitivity.ordF_semantics (M := M),decision_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- The complete source proof, with the actual internal Child induction. -/
theorem ordF_eq_check_le (hM : FirstOrder.Theory.Models M nativeZF) {k j : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {A : Formula (j+2)} {ap : Fin j → M.Carrier .set} {P top G F : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hdomain : ∀ s, Predicate H lp s ↔ HS A ap G P F s)
    (hcheck : ∀ x nx, Checked top x nx → Predicate H lp nx) :
    ∀ sigma p a, Predicate H lp sigma → (Project.FirstOrderSemantics.reduct M).mem p P →
      Rank sigma a → OrdF L H lp P p sigma → Decision L lp P top sigma p a := by
  classical
  let inputs : Fin (k+2) → M.Carrier .set := Fin.lastCases top (Fin.lastCases P lp)
  let matrix := inductionAt L H (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))
  have hm : ∀ sigma, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases sigma inputs) matrix ↔ (Predicate H lp sigma → ∀ p a,
        (Project.FirstOrderSemantics.reduct M).mem p P → Rank sigma a →
        OrdF L H lp P p sigma → Decision L lp P top sigma p a) := by
    intro sigma
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      inductionAt_semantics (M := M) (Fin.lastCases sigma inputs) L H
        (fun i => i.castSucc.castSucc.castSucc) (Fin.last k).castSucc.castSucc
        (Fin.last (k+1)).castSucc (Fin.last (k+2))
  have all := ForcingMapLaws.formula_induction hM matrix inputs (by
    intro sigma ih
    apply (hm sigma).mpr
    intro hs p a hp hra ho
    have ha := (ForcingRawRank.rank_spec.mp hra).1.1
    obtain ⟨na,hna⟩ := ForcingCheckName.exists_checked hM top a
    have hbounded : ∀ nu q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
        Forces false L lp P nu sigma q → Forces false L lp P nu na q := by
      intro nu q hq hqp hmem
      apply (ForcingInfinity.mem_check hM hna ht htop hq).mpr
      intro r hr hrq
      obtain ⟨s,tau,c,hsc,hsr,hc,he,hscle,heq⟩ :=
        ((ForcingAtomicRelations.mem_iff hM L lp P nu sigma q).mp hmem).2 r hr hrq
      have htau := (hdomain tau).mpr (ForcingHS.child ((hdomain sigma).mp hs) he)
      have hsp := hpre.2 s q p hsc hq hp (hpre.2 s r q hsc hr hq hsr hrq) hqp
      have hmemtau := ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hscle he
        (ForcingAtomicBasic.eq_refl hM hpre tau s hsc)
      obtain ⟨b,hrb⟩ := ForcingRawRank.exists_rank hM tau
      obtain ⟨t,htc,hts,beta,hbeta,hbetab,nb,hnb,hetau⟩ :=
        (hm tau).mp (ih tau c he) htau s b hsc hrb
          (ForcingOrdinalTransitivity.ordF_mem hM hpre htau
            (ForcingOrdinalTransitivity.ordF_mono hpre hp hsc hsp ho) hmemtau)
      have hba := ForcingRawRank.child_rank_lt hM hra hrb he
      have hbetaa : (Project.FirstOrderSemantics.reduct M).mem beta a := by
        rcases hbetab with rfl | hlt
        · exact hba
        · exact ForcingRawRank.ordinal_transitive ha b hba beta hlt
      exact ⟨t,htc,hpre.2 t s r htc hsc hr hts hsr,beta,hbetaa,nb,hnb,
        ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre htc hts heq) hetau⟩
    have hmiss : ∀ nx, Checked top a nx → ¬Forces false L lp P nx sigma p := by
      intro nx hnx hmem
      have he := ForcingCheckName.unique hM hnx hna
      subst nx
      exact ordinal_irrefl hM ha ((ForcingCheckReflection.mem_check_check hM hpre ht htop hp hna hna).mp
        (hbounded na p hp (hpre.1 p hp) hmem))
    obtain ⟨alpha,halpha,hmissalpha,hmin⟩ := least_missing hM L lp P top sigma p a ha hmiss
    have halphaa := hmin a ha hmiss
    obtain ⟨nalpha,hnalpha⟩ := ForcingCheckName.exists_checked hM top alpha
    have hbelow : ∀ beta, (Project.FirstOrderSemantics.reduct M).mem beta alpha →
        ∀ nb, Checked top beta nb → Forces false L lp P nb sigma p := by
      intro beta hba nb hnb
      apply Classical.byContradiction
      intro hn
      have hmissb : ∀ nc, Checked top beta nc → ¬Forces false L lp P nc sigma p := by
        intro nc hnc
        have he := ForcingCheckName.unique hM hnc hnb
        exact he.symm ▸ hn
      rcases hmin beta (ForcingRawRank.ordinal_member hM halpha hba) hmissb with he | hab
      · exact ordinal_irrefl hM halpha (he.symm ▸ hba)
      · exact ordinal_irrefl hM halpha (ForcingRawRank.ordinal_transitive halpha beta hba alpha hab)
    have hneg : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel L lp q p ∧
        ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel L lp r q →
          ¬Forces false L lp P nalpha sigma r := by
      apply Classical.byContradiction
      intro hn
      apply hmissalpha nalpha hnalpha
      apply ForcingAtomicBasic.mem_of_dense hM hpre hp
      intro q hq hqp
      apply Classical.byContradiction
      intro hnone
      apply hn
      refine ⟨q,hq,hqp,?_⟩
      intro r hr hrq hf
      exact hnone ⟨r,hr,hrq,hf⟩
    obtain ⟨q,hq,hqp,hnegq⟩ := hneg
    refine ⟨q,hq,hqp,alpha,halpha,halphaa,nalpha,hnalpha,?_⟩
    apply ForcingBasicSetAxioms.eq_of_same_members hM hpre ((hdomain sigma).mp hs)
      ((hdomain nalpha).mp (hcheck alpha nalpha hnalpha)) hq
    intro nu _ r hr hrq
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    constructor
    · intro hmem
      apply (ForcingInfinity.mem_check hM hnalpha ht htop hr).mpr
      intro s hsc hsr
      obtain ⟨t,htc,hts,beta,hbetaa,nb,hnb,he⟩ :=
        (ForcingInfinity.mem_check hM hna ht htop hr).mp (hbounded nu r hr hrp hmem) s hsc hsr
      have htr := hpre.2 t s r htc hsc hr hts hsr
      have htq := hpre.2 t r q htc hr hq htr hrq
      have htp := hpre.2 t q p htc hq hp htq hqp
      have hbmem := (ForcingAtomicLaws.mem_congr_left hM hpre he).mp
        (ForcingAtomicBasic.mem_mono hM hpre htc htr hmem)
      have hbetaalpha : (Project.FirstOrderSemantics.reduct M).mem beta alpha := by
        rcases ordinal_compare hM (ForcingRawRank.ordinal_member hM ha hbetaa) halpha with heq | hlt | hgt
        · have hname := ForcingCheckName.unique hM (heq ▸ hnb) hnalpha
          exact False.elim (hnegq t htc htq (hname ▸ hbmem))
        · exact hlt
        · exact False.elim (hnegq t htc htq (ho.1 nb (hcheck beta nb hnb) nalpha
            (hcheck alpha nalpha hnalpha) t htc htp hbmem
              (ForcingInfinity.check_mem_of_mem hM hpre hnb hnalpha hgt ht htop htc)))
      exact ⟨t,htc,hts,beta,hbetaalpha,nb,hnb,he⟩
    · intro hmem
      apply ForcingAtomicBasic.mem_of_dense hM hpre hr
      intro s hsc hsr
      obtain ⟨t,htc,hts,beta,hba,nb,hnb,he⟩ :=
        (ForcingInfinity.mem_check hM hnalpha ht htop hr).mp hmem s hsc hsr
      have htp := hpre.2 t r p htc hr hp (hpre.2 t s r htc hsc hr hts hsr) hrp
      exact ⟨t,htc,hts,(ForcingAtomicLaws.mem_congr_left hM hpre he).mpr
        (ForcingAtomicBasic.mem_mono hM hpre htc htp (hbelow beta hba nb hnb))⟩)
  intro sigma p a hs hp hr ho
  exact (hm sigma).mp (all sigma) hs p a hp hr ho

/-- Exact source dense decision, retaining the quantitative bound as well. -/
theorem forces_ordinal_decide (hM : FirstOrder.Theory.Models M nativeZF) {k j n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {A : Formula (j+2)} {ap : Fin j → M.Carrier .set} {P top G F p a : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hdomain : ∀ s, Predicate H lp s ↔ HS A ap G P F s)
    (hcheck : ∀ x nx, Checked top x nx → Predicate H lp nx)
    (v : Fin n → M.Carrier .set) (x : Fin n) (hs : Predicate H lp (v x))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hra : Rank (v x) a)
    (ho : ForcingFormula.Force L H lp v P p (Source.SetLanguage.ordinal x)) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
      Decision L lp P top (v x) q a := by
  intro q hq hqp
  exact ordF_eq_check_le hM hpre ht htop hdomain hcheck (v x) q a hs hq hra
    (ForcingOrdinalTransitivity.ordF_mono hpre hp hq hqp
      (ForcingOrdinalTransitivity.ordF_of_forces_ordinal hM hpre hp v x ho))

def denseDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top sigma p a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) P.castSucc).imp ((rel L (paramsUp lp) (Fin.last m) p.castSucc).imp
    (decision L (paramsUp lp) P.castSucc top.castSucc sigma.castSucc (Fin.last m) a.castSucc)))

theorem denseDecision_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top sigma p a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (denseDecision L lp P top sigma p a) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) →
        MapRel L (fun i => env (lp i)) q (env p) →
        Decision L (fun i => env (lp i)) (env P) (env top) (env sigma) q (env a) := by
  simp only [denseDecision,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    decision_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Both source statements for the existing concrete product system. All
preorder, top and check-HS inputs are produced from its actual presentation. -/
def decisionSentence {n : Nat} (fullOrdinal : Bool) (rho : Fin 7 → Fin n)
    (G F mul unit I K B w top sigma p a : Fin n) : Source.Sentence :=
  let L := ForcingProductSymmetry.orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  let premise := if fullOrdinal then ForcingFormula.formula L H id (Source.SetLanguage.args1 sigma)
    (rho 6) p (Source.SetLanguage.ordinal (0 : Fin 1)) else ordF L H id (rho 6) p sigma
  let conclusion := if fullOrdinal then denseDecision L id (rho 6) top sigma p a
    else decision L id (rho 6) top sigma p a
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit).imp
    ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
      ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
        ((ForcingWithTopCarrier.empty top).imp ((MinimalPredicates.pred H id sigma).imp
          ((Formula.mem p (rho 6)).imp ((LayerRankSyntax.rank sigma a).imp (premise.imp conclusion))))))))).close

theorem decision_models {n : Nat} (fullOrdinal : Bool) (rho : Fin 7 → Fin n)
    (G F mul unit I K B w top sigma p a : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (decisionSentence fullOrdinal rho G F mul unit I K B w top sigma p a)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hpresentation hG hF ht hs hp hra ho
  let L := ForcingProductSymmetry.orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul unit).mp hm
  have hpres := (ForcingProductFamily.presentation_semantics (M := M) env
    (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpresentation
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm'
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have ht' := (ForcingWithTopCarrier.empty_semantics (M := M) env top).mp ht
  have htP := (hpres.2.2.2.2.2 (env top)).mpr (Or.inl ht')
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel L env q (env top) :=
    fun q _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht')
  have hdomain := fun s => ForcingPairUnion.domain_semantics env rho G F s
  have hcheck : ∀ x nx, Checked (env top) x nx → Predicate H env nx := by
    intro x nx hn
    exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun i => env (rho i)) hpres hG' hF' ht' hn)
  have hs' := (ForcingClassEvaluation.predicate_semantics (M := M) env H id sigma).mp hs
  have hra' := (rank_semantics (M := M) env sigma a).mp hra
  cases fullOrdinal with
  | false =>
    apply (decision_semantics (M := M) env L id (rho 6) top sigma p a).mpr
    exact ordF_eq_check_le hM hpre htP htop hdomain hcheck (env sigma) (env p) (env a) hs' hp hra'
      ((ForcingOrdinalTransitivity.ordF_semantics (M := M) env L H id (rho 6) p sigma).mp ho)
  | true =>
    apply (denseDecision_semantics (M := M) env L id (rho 6) top sigma p a).mpr
    have ho' := (ForcingFormula.formula_semantics (M := M) env L H id (Source.SetLanguage.args1 sigma)
      (rho 6) p (Source.SetLanguage.ordinal (0 : Fin 1))).mp ho
    exact forces_ordinal_decide hM hpre htP htop hdomain hcheck
      (fun i => env (Source.SetLanguage.args1 sigma i)) 0 hs' hp hra' ho'

theorem decision_kernel_certificate {n : Nat} (fullOrdinal : Bool) (rho : Fin 7 → Fin n)
    (G F mul unit I K B w top sigma p a : Fin n) : FirstOrder.Derives nativeZF []
      (Translation.sentence (decisionSentence fullOrdinal rho G F mul unit I K B w top sigma p a)) :=
  ModelTransfer.derives (fun _ hM => decision_models fullOrdinal rho G F mul unit I K B w top sigma p a hM)

end PPAC.Migration.ForcingOrdinalDecision
