/- Pinned UniformNames.transF_checkOrdinal:336, ordF_checkOrdinal:343,
forces_membershipWellFounded:354, forces_checkOrdinal:381 and
ClassFibers.wellorderableFormula:12, wellorderable:15, forces_wellorderable:27,
wellorderable_of_check_injection:65, no_check_injection_of_not_wellorderable:73.
Uses the SAME pure-set forcing relation, check names and internal ordinals in
every nativeZF model without Choice or external well-foundedness. -/
import PPAC.Migration.ForcingOrdinalDecision
import PPAC.Migration.ForcingFoundation

namespace PPAC.Migration.ForcingCheckOrdinal
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ReplacementPredicates (paramsUp rel)
open MinimalPredicates (pred)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force formula)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Ordinal ordinal_semantics)
open ForcingClassEvaluation (Predicate)
open ForcingOrdinalTransitivity (TransF OrdF transF ordF)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- A set is wellorderable exactly when it embeds in some ordinal. Both
quantified witnesses are internal sets; the injection is an internal graph. -/
def wellorderableFormula : Formula 1 :=
  .ex ((Source.SetLanguage.ordinal 1).conj (.ex (Source.SetLanguage.injection 2 0 1)))

def wellorderable {n : Nat} (a : Fin n) : Formula n :=
  wellorderableFormula.rename (args1 a)

theorem transF_checkOrdinal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P top alpha name p : M.Carrier .set}
    (hpre : PreorderOn L lp P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (halpha : Ordinal alpha) (hn : Checked top alpha name) :
    TransF L H lp P p name := by
  intro nu _ chi _ q hq _ hnu hchi
  apply (ForcingInfinity.mem_check hM hn ht htop hq).mpr
  intro r hr hrq
  obtain ⟨r1,hr1,hr1r,beta,hbeta,nb,hnb,hnuEq⟩ :=
    (ForcingInfinity.mem_check hM hn ht htop hq).mp hnu r hr hrq
  have hchi' : Forces false L lp P chi nb r1 :=
    (ForcingAtomicLaws.mem_congr_right hM hpre hnuEq).mp
      (ForcingAtomicBasic.mem_mono hM hpre hr1 (hpre.2 r1 r q hr1 hr hq hr1r hrq) hchi)
  obtain ⟨r2,hr2,hr2r1,gamma,hgamma,ng,hng,hchiEq⟩ :=
    (ForcingInfinity.mem_check hM hnb ht htop hr1).mp hchi' r1 hr1 (hpre.1 r1 hr1)
  exact ⟨r2,hr2,hpre.2 r2 r1 r hr2 hr1 hr hr2r1 hr1r,gamma,
    ForcingRawRank.ordinal_transitive halpha beta hbeta gamma hgamma,ng,hng,hchiEq⟩

theorem ordF_checkOrdinal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P top alpha name p : M.Carrier .set}
    (hpre : PreorderOn L lp P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (halpha : Ordinal alpha) (hn : Checked top alpha name) :
    OrdF L H lp P p name := by
  refine ⟨transF_checkOrdinal hM hpre ht htop halpha hn,?_⟩
  intro nu _ q hq _ hnu chi hchi psi hpsi r hr hrq hchiM hpsiM
  apply ForcingAtomicBasic.mem_of_dense hM hpre hr
  intro s hs hsr
  obtain ⟨t,htc,hts,beta,hbeta,nb,hnb,hnuEq⟩ :=
    (ForcingInfinity.mem_check hM hn ht htop hq).mp hnu s hs (hpre.2 s r q hs hr hq hsr hrq)
  have htr := hpre.2 t s r htc hs hr hts hsr
  have htrans : TransF L H lp P t nu :=
    (ForcingOrdinalTransitivity.transF_congr hM hpre hnuEq).mpr
      (transF_checkOrdinal hM hpre ht htop (ForcingRawRank.ordinal_member hM halpha hbeta) hnb)
  exact ⟨t,htc,hts,htrans chi hchi psi hpsi t htc (hpre.1 t htc)
    (ForcingAtomicBasic.mem_mono hM hpre htc htr hchiM)
    (ForcingAtomicBasic.mem_mono hM hpre htc htr hpsiM)⟩

/-- Internal name induction forces internal membership well-foundedness for
every name, before checking transitivity or linearity. -/
theorem forces_membershipWellFounded (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (hchild : ∀ nu, Predicate H lp nu → ∀ chi c, PureKuratowski.PairMember M chi c nu → Predicate H lp chi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a : Fin n) :
    Force L H lp v P p (Source.SetLanguage.membershipWellFounded a) := by
  unfold Source.SetLanguage.membershipWellFounded
  rw [ForcingSound.rename hM hpre _ _ _ _ hp]
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro b hb
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq hqp hsubnon
  have hnon : Force L H lp _ P q (Source.SetLanguage.nonempty 1) := hsubnon.2
  unfold Source.SetLanguage.nonempty at hnon
  rw [ForcingSound.rename hM hpre _ _ _ _ hq] at hnon
  apply (ForcingFormula.force_ex L H lp _ P q _).mpr
  intro r hr hrq
  obtain ⟨r1,hr1,hr1r,x,hx,hxb⟩ :=
    (ForcingFormula.force_ex L H lp _ P q _).mp hnon r hr hrq
  have hxb' : Forces false L lp P x b r1 := hxb
  obtain ⟨r2,hr2,hr2r1,y,hy,hyb,hmin⟩ :=
    ForcingFoundation.minimal_member hM L H lp P b hpre hchild x r1 hx hxb'
  refine ⟨r2,hr2,hpre.2 r2 r1 r hr2 hr1 hr hr2r1 hr1r,y,hy,hyb,?_⟩
  apply (ForcingFormula.force_all hM hpre hr2 _ _).mpr
  intro z hz
  apply (ForcingFormula.force_imp hM hpre hr2 _ _ _).mpr
  intro s hs hsr2 hzb
  apply (ForcingFormula.force_neg hM hpre hs _ _).mpr
  intro t htc hts hzy
  have hzb' : Forces false L lp P z b s := hzb
  have hzy' : Forces false L lp P z y t := hzy
  exact hmin z hz t htc (hpre.2 t s r2 htc hs hr2 hts hsr2)
    hzy' (ForcingAtomicBasic.mem_mono hM hpre htc hts hzb')

theorem forces_checkOrdinal (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P top alpha p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hchild : ∀ nu, Predicate H lp nu → ∀ chi c, PureKuratowski.PairMember M chi c nu → Predicate H lp chi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a : Fin n)
    (halpha : Ordinal alpha) (hn : Checked top alpha (v a)) :
    Force L H lp v P p (Source.SetLanguage.ordinal a) := by
  have hlin : Force L H lp v P p (Source.SetLanguage.membershipLinear a) := by
    unfold Source.SetLanguage.membershipLinear
    rw [ForcingSound.rename hM hpre _ _ _ _ hp,
      ForcingFormula.force_conj,ForcingFormula.force_conj]
    refine ⟨?_,?_,?_⟩
    · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro x _
      apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
      intro q hq _ hxa
      apply (ForcingFormula.force_neg hM hpre hq _ _).mpr
      intro r hr hrq hxx
      have hxa' : Forces false L lp P x (v a) q := hxa
      have hxx' : Forces false L lp P x x r := hxx
      obtain ⟨s,hs,hsr,beta,hbeta,nb,hnb,hxEq⟩ :=
        (ForcingInfinity.mem_check hM hn ht htop hq).mp hxa' r hr hrq
      have hbb : Forces false L lp P nb nb s :=
        (ForcingAtomicLaws.mem_congr_right hM hpre hxEq).mp
          ((ForcingAtomicLaws.mem_congr_left hM hpre hxEq).mp
            (ForcingAtomicBasic.mem_mono hM hpre hs hsr hxx'))
      exact ForcingOrdinalDecision.ordinal_irrefl hM
        (ForcingRawRank.ordinal_member hM halpha hbeta)
        ((ForcingCheckReflection.mem_check_check hM hpre ht htop hs hnb hnb).mp hbb)
    · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro x hx
      apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro y hy
      apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro z hz
      apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
      intro q1 hq1 hq1p _
      apply (ForcingFormula.force_imp hM hpre hq1 _ _ _).mpr
      intro q2 hq2 hq2q1 _
      apply (ForcingFormula.force_imp hM hpre hq2 _ _ _).mpr
      intro q3 hq3 hq3q2 hza
      apply (ForcingFormula.force_imp hM hpre hq3 _ _ _).mpr
      intro r hr hrq3 hxy_yz
      have hza' : Forces false L lp P z (v a) q3 := hza
      have hxy : Forces false L lp P x y r := hxy_yz.1
      have hyz : Forces false L lp P y z r := hxy_yz.2
      have hord := ordF_checkOrdinal hM (H := H) hpre ht htop halpha hn (p := p)
      have hq3p := hpre.2 q3 q1 p hq3 hq1 hp (hpre.2 q3 q2 q1 hq3 hq2 hq1 hq3q2 hq2q1) hq1p
      exact (hord.2 z hz q3 hq3 hq3p hza') y hy x hx r hr hrq3 hyz hxy
    · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro x _
      apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro y _
      apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
      intro q1 hq1 _ hxa
      apply (ForcingFormula.force_imp hM hpre hq1 _ _ _).mpr
      intro q2 hq2 hq2q1 hya
      have hxa' : Forces false L lp P x (v a) q1 := hxa
      have hya' : Forces false L lp P y (v a) q2 := hya
      apply (ForcingFormula.force_disj L H lp _ P q2 _ _).mpr
      intro r hr hrq2
      obtain ⟨r1,hr1,hr1r,beta,hbeta,nb,hnb,hxEq⟩ :=
        (ForcingInfinity.mem_check hM hn ht htop hq1).mp hxa' r hr
          (hpre.2 r q2 q1 hr hq2 hq1 hrq2 hq2q1)
      obtain ⟨r2,hr2,hr2r1,gamma,hgamma,ng,hng,hyEq⟩ :=
        (ForcingInfinity.mem_check hM hn ht htop hq2).mp hya' r1 hr1
          (hpre.2 r1 r q2 hr1 hr hq2 hr1r hrq2)
      have hr2r := hpre.2 r2 r1 r hr2 hr1 hr hr2r1 hr1r
      have hxEq' := ForcingAtomicBasic.eq_mono hM hpre hr2 hr2r1 hxEq
      rcases ForcingOrdinalDecision.ordinal_compare hM
        (ForcingRawRank.ordinal_member hM halpha hbeta)
        (ForcingRawRank.ordinal_member hM halpha hgamma) with heq | hlt | hgt
      · have hbg : Forces true L lp P nb ng r2 :=
          (ForcingCheckReflection.eq_check_iff hM hpre ht htop hr2 hnb hng).mpr heq
        have hxy : Forces true L lp P x y r2 :=
          ForcingAtomicLaws.eq_trans hM hpre hxEq'
            (ForcingAtomicLaws.eq_trans hM hpre hbg (ForcingAtomicBasic.eq_symm hM hyEq))
        exact ⟨r2,hr2,hr2r,Or.inl hxy⟩
      · refine ⟨r2,hr2,hr2r,Or.inr ?_⟩
        apply (ForcingFormula.force_disj L H lp _ P r2 _ _).mpr
        intro s hs hsr2
        have hbg : Forces false L lp P nb ng s :=
          ForcingInfinity.check_mem_of_mem hM hpre hng hnb hlt ht htop hs
        have hxy : Forces false L lp P x y s :=
          (ForcingAtomicLaws.mem_congr_left hM hpre
            (ForcingAtomicBasic.eq_mono hM hpre hs hsr2 hxEq')).mpr
            ((ForcingAtomicLaws.mem_congr_right hM hpre
              (ForcingAtomicBasic.eq_mono hM hpre hs hsr2 hyEq)).mpr hbg)
        exact ⟨s,hs,hpre.1 s hs,Or.inl hxy⟩
      · refine ⟨r2,hr2,hr2r,Or.inr ?_⟩
        apply (ForcingFormula.force_disj L H lp _ P r2 _ _).mpr
        intro s hs hsr2
        have hgb : Forces false L lp P ng nb s :=
          ForcingInfinity.check_mem_of_mem hM hpre hnb hng hgt ht htop hs
        have hyx : Forces false L lp P y x s :=
          (ForcingAtomicLaws.mem_congr_left hM hpre
            (ForcingAtomicBasic.eq_mono hM hpre hs hsr2 hyEq)).mpr
            ((ForcingAtomicLaws.mem_congr_right hM hpre
              (ForcingAtomicBasic.eq_mono hM hpre hs hsr2 hxEq')).mpr hgb)
        exact ⟨s,hs,hpre.1 s hs,Or.inr hyx⟩
  exact ⟨(ForcingOrdinalTransitivity.forces_transitiveSet hM hpre hp v a).mpr
    (transF_checkOrdinal hM hpre ht htop halpha hn),
    hlin,forces_membershipWellFounded hM hpre hchild hp v a⟩

theorem forces_wellorderable (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a : Fin n) :
    Force L H lp v P p (wellorderable a) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L lp r q ∧
          ∃ eta, Predicate H lp eta ∧ Force L H lp (args1 eta) P r (Source.SetLanguage.ordinal 0) ∧
            ∀ s, (Project.FirstOrderSemantics.reduct M).mem s P → MapRel L lp s r →
              ∃ t, (Project.FirstOrderSemantics.reduct M).mem t P ∧ MapRel L lp t s ∧
                ∃ J, Predicate H lp J ∧ Force L H lp (args3 J (v a) eta) P t (Source.SetLanguage.injection 0 1 2) := by
  unfold wellorderable wellorderableFormula
  rw [ForcingSound.rename hM hpre _ _ _ _ hp]
  have hord : ∀ eta r, (Project.FirstOrderSemantics.reduct M).mem r P →
      (Force L H lp (Fin.lastCases eta (fun i => v (args1 a i))) P r (Source.SetLanguage.ordinal 1) ↔
        Force L H lp (args1 eta) P r (Source.SetLanguage.ordinal 0)) := by
    intro eta r hr
    unfold Source.SetLanguage.ordinal Source.SetLanguage.transitiveSet
      Source.SetLanguage.membershipLinear Source.SetLanguage.membershipWellFounded
    rw [ForcingFormula.force_conj,ForcingFormula.force_conj,
      ForcingFormula.force_conj,ForcingFormula.force_conj,
      ForcingSound.rename hM hpre _ _ _ _ hr,ForcingSound.rename hM hpre _ _ _ _ hr,
      ForcingSound.rename hM hpre _ _ _ _ hr,ForcingSound.rename hM hpre _ _ _ _ hr,
      ForcingSound.rename hM hpre _ _ _ _ hr,ForcingSound.rename hM hpre _ _ _ _ hr]
    have hv : (fun i : Fin 1 => Fin.lastCases eta (fun j => v (args1 a j)) (args1 (1 : Fin 2) i)) =
        (fun i : Fin 1 => args1 eta (args1 (0 : Fin 1) i)) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      rfl
    rw [hv]
  have hinj : ∀ eta J t, (Project.FirstOrderSemantics.reduct M).mem t P →
      (Force L H lp (Fin.lastCases J (Fin.lastCases eta (fun i => v (args1 a i)))) P t
          (Source.SetLanguage.injection 2 0 1) ↔
        Force L H lp (args3 J (v a) eta) P t (Source.SetLanguage.injection 0 1 2)) := by
    intro eta J t ht
    unfold Source.SetLanguage.injection
    rw [ForcingSound.rename hM hpre _ _ _ _ ht,ForcingSound.rename hM hpre _ _ _ _ ht]
    have hv : (fun i : Fin 3 => Fin.lastCases J (Fin.lastCases eta (fun j => v (args1 a j)))
          (args3 (2 : Fin 3) 0 1 i)) =
        (fun i : Fin 3 => args3 J (v a) eta (args3 (0 : Fin 3) 1 2 i)) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun m => Fin.cases ?_ (fun z => Fin.elim0 z) m) j) i <;> rfl
    rw [hv]
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,eta,heta,h1,h2⟩ := h q hq hqp
    refine ⟨r,hr,hrq,eta,heta,(hord eta r hr).mp h1,?_⟩
    intro s hs hsr
    obtain ⟨t,ht,hts,J,hJ,h3⟩ := h2 s hs hsr
    exact ⟨t,ht,hts,J,hJ,(hinj eta J t ht).mp h3⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,eta,heta,h1,h2⟩ := h q hq hqp
    refine ⟨r,hr,hrq,eta,heta,(hord eta r hr).mpr h1,?_⟩
    intro s hs hsr
    obtain ⟨t,ht,hts,J,hJ,h3⟩ := h2 s hs hsr
    exact ⟨t,ht,hts,J,hJ,(hinj eta J t ht).mpr h3⟩

/-- Injecting a set into a checked ordinal is enough for the genuine
wellorderability formula. No ordinal preservation assumption is used. -/
theorem wellorderable_of_check_injection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P top Y J alpha nalpha p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hchild : ∀ nu, Predicate H lp nu → ∀ chi c, PureKuratowski.PairMember M chi c nu → Predicate H lp chi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (halpha : Ordinal alpha) (hnalpha : Checked top alpha nalpha)
    (hdomAlpha : Predicate H lp nalpha) (hdomJ : Predicate H lp J)
    (hinj : Force L H lp (args3 J Y nalpha) P p (Source.SetLanguage.injection 0 1 2)) :
    Force L H lp (args1 Y) P p (wellorderable 0) := by
  rw [forces_wellorderable hM hpre hp]
  intro q hq hqp
  refine ⟨q,hq,hpre.1 q hq,nalpha,hdomAlpha,
    forces_checkOrdinal hM hpre ht htop hchild hq (args1 nalpha) 0 halpha hnalpha,?_⟩
  intro s hs hsq
  exact ⟨s,hs,hpre.1 s hs,J,hdomJ,
    ForcingFormula.mono hM hpre _ _ hp hs (hpre.2 s q p hs hq hp hsq hqp) hinj⟩

theorem no_check_injection_of_not_wellorderable (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P top Y alpha nalpha p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hchild : ∀ nu, Predicate H lp nu → ∀ chi c, PureKuratowski.PairMember M chi c nu → Predicate H lp chi)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hnot : Force L H lp (args1 Y) P p (wellorderable 0).neg)
    (halpha : Ordinal alpha) (hnalpha : Checked top alpha nalpha)
    (hdomAlpha : Predicate H lp nalpha) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
      ∀ J, Predicate H lp J →
        ¬Force L H lp (args3 J Y nalpha) P q (Source.SetLanguage.injection 0 1 2) := by
  intro q hq hqp J hdomJ hinj
  exact (ForcingFormula.force_neg hM hpre hp _ _).mp hnot q hq hqp
    (wellorderable_of_check_injection hM hpre ht htop hchild hq halpha hnalpha hdomAlpha hdomJ hinj)

def childClosed {k m : Nat} (H : Formula (k+1)) (lp : Fin k → Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let nu := (Fin.last m).castSucc.castSucc
  let chi := (Fin.last (m+1)).castSucc
  let c := Fin.last (m+2)
  .all ((pred H (paramsUp lp) (Fin.last m)).imp
    (.all (.all ((Source.SetLanguage.edge nu chi c).imp
      (pred H (fun i => up (lp i)) chi)))))

theorem childClosed_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (H : Formula (k+1)) (lp : Fin k → Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (childClosed H lp) ↔
      ∀ nu, Predicate H (fun i => env (lp i)) nu → ∀ chi c,
        PureKuratowski.PairMember M chi c nu → Predicate H (fun i => env (lp i)) chi := by
  simp only [childClosed,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    KuratowskiZF.source_edge,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (P top alpha nalpha Y J p : Fin m) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder L lp P).imp ((Formula.mem top P).imp
    ((Formula.all ((Formula.mem (Fin.last m) P.castSucc).imp
      (rel L (paramsUp lp) (Fin.last m) top.castSucc))).imp
    ((childClosed H lp).imp ((Formula.mem p P).imp
      ((OrdinalSyntax.ordinal alpha).imp ((checkName top alpha nalpha).imp
        ((ordF L H lp P p nalpha).conj
          ((formula L H lp (args1 Y) P p (Source.SetLanguage.membershipWellFounded 0)).conj
            ((formula L H lp (args1 nalpha) P p (Source.SetLanguage.ordinal 0)).conj
              (((pred H lp nalpha).imp ((pred H lp J).imp
                ((formula L H lp (args3 J Y nalpha) P p (Source.SetLanguage.injection 0 1 2)).imp
                  (formula L H lp (args1 Y) P p (wellorderable 0))))).conj
                (((formula L H lp (args1 Y) P p (wellorderable 0).neg).imp
                  ((pred H lp nalpha).imp ((pred H lp J).imp
                    (formula L H lp (args3 J Y nalpha) P p (Source.SetLanguage.injection 0 1 2)).neg))))))))))))))).close

theorem models {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (P top alpha nalpha Y J p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence L H lp P top alpha nalpha Y J p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre ht htop hchild hp halpha hnalpha
  have hpre' := (ForcingAtomicBasic.preorder_semantics (M := M) env L lp P).mp hpre
  have htop' : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) →
      MapRel L (fun i => env (lp i)) q (env top) := by
    intro q hq
    have hq' : Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases q env)
        (.mem (Fin.last m) P.castSucc) := by
      simpa only [Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc] using hq
    let vq : Fin (m+1) → M.Carrier .set := Fin.lastCases q env
    have h := (ForcingMapConditions.rel_semantics (M := M) vq L
      (paramsUp lp) (Fin.last m) top.castSucc).mp (htop q hq')
    simpa only [vq,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using h
  have hchild' := (childClosed_semantics (M := M) env H lp).mp hchild
  have halpha' := (ordinal_semantics (M := M) env alpha).mp halpha
  have hnalpha' := (ForcingCheckName.checkName_semantics (M := M) env top alpha nalpha).mp hnalpha
  have harg1 (x : Fin m) : (fun i : Fin 1 => env (args1 x i)) = args1 (env x) := by
    funext i
    refine Fin.cases rfl (fun j => Fin.elim0 j) i
  have harg3 (x y z : Fin m) : (fun i : Fin 3 => env (args3 x y z i)) = args3 (env x) (env y) (env z) := by
    funext i
    refine Fin.cases rfl (fun j => Fin.cases rfl (fun l => Fin.cases rfl (fun w => Fin.elim0 w) l) j) i
  refine ⟨(ForcingOrdinalTransitivity.ordF_semantics (M := M) env L H lp P p nalpha).mpr
    (ordF_checkOrdinal hM hpre' ht htop' halpha' hnalpha'),?_,?_,?_,?_⟩
  · apply (ForcingFormula.formula_semantics (M := M) env L H lp (args1 Y) P p
      (Source.SetLanguage.membershipWellFounded 0)).mpr
    rw [harg1 Y]
    exact forces_membershipWellFounded hM hpre' hchild' hp (args1 (env Y)) 0
  · apply (ForcingFormula.formula_semantics (M := M) env L H lp (args1 nalpha) P p
      (Source.SetLanguage.ordinal 0)).mpr
    rw [harg1 nalpha]
    exact forces_checkOrdinal hM hpre' ht htop' hchild' hp (args1 (env nalpha)) 0 halpha' hnalpha'
  · intro hdomAlpha hdomJ hinj
    have hdomAlpha' := (ForcingClassEvaluation.predicate_semantics (M := M) env H lp nalpha).mp hdomAlpha
    have hdomJ' := (ForcingClassEvaluation.predicate_semantics (M := M) env H lp J).mp hdomJ
    have hinj' := (ForcingFormula.formula_semantics (M := M) env L H lp (args3 J Y nalpha) P p
      (Source.SetLanguage.injection 0 1 2)).mp hinj
    rw [harg3 J Y nalpha] at hinj'
    apply (ForcingFormula.formula_semantics (M := M) env L H lp (args1 Y) P p (wellorderable 0)).mpr
    rw [harg1 Y]
    exact wellorderable_of_check_injection hM hpre' ht htop' hchild' hp halpha' hnalpha' hdomAlpha' hdomJ' hinj'
  · intro hnot hdomAlpha hdomJ hinj
    have hnot' := (ForcingFormula.formula_semantics (M := M) env L H lp (args1 Y) P p (wellorderable 0).neg).mp hnot
    rw [harg1 Y] at hnot'
    have hdomAlpha' := (ForcingClassEvaluation.predicate_semantics (M := M) env H lp nalpha).mp hdomAlpha
    have hdomJ' := (ForcingClassEvaluation.predicate_semantics (M := M) env H lp J).mp hdomJ
    have hinj' := (ForcingFormula.formula_semantics (M := M) env L H lp (args3 J Y nalpha) P p
      (Source.SetLanguage.injection 0 1 2)).mp hinj
    rw [harg3 J Y nalpha] at hinj'
    exact no_check_injection_of_not_wellorderable hM hpre' ht htop' hchild' hp hnot' halpha' hnalpha' hdomAlpha'
      (env p) hp (hpre'.1 (env p) hp) (env J) hdomJ' hinj'

theorem kernel_certificate {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (P top alpha nalpha Y J p : Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence L H lp P top alpha nalpha Y J p)) :=
  ModelTransfer.derives (fun _ hM => models L H lp P top alpha nalpha Y J p hM)

end PPAC.Migration.ForcingCheckOrdinal
