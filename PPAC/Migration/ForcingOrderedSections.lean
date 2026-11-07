/- Pinned OrderedSections.wellorderable_check_dense:173-189.
Consume existing FULL wellorderable forcing, internal ordinal decision/rank,
check-name HS and tuple congruence. No new foundation or ordinal cutoff. -/
import PPAC.Migration.ForcingLeastOccurrence
import PPAC.Migration.ForcingCheckOrdinal

namespace PPAC.Migration.ForcingOrderedSections
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args3)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingCheckName (Checked)
open ForcingRawRank (Ordinal)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- An actual internal ordinal/check/injection witness below q. -/
def Witness {k : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P top X q : M.Carrier .set) : Prop :=
  ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧
    ∃ beta, Ordinal beta ∧ ∃ checked, Checked top beta checked ∧
      ∃ J, Predicate H env J ∧ Force L H env (args3 J X checked) P r (Source.SetLanguage.injection 0 1 2)

theorem wellorderable_check_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top : Fin k)
    {X p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hWo : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 X)
      (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0)) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q p →
        Witness (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env top) X q := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hCheck : ∀ x checked, Checked (env top) x checked → Predicate H env checked := by
    intro x checked hc
    apply (domain_semantics env rho G F checked).mpr
    apply ForcingHSCheck.check_hs hM actionFormula v7 (env G) W (env F) (env top) hF.1 htW ?_ x checked hc
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hPres ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v7 pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hPres ht ha⟩⟩
  intro q hq hqp
  obtain ⟨r,hr,hrq,eta,hEta,ho,hInj⟩ := (ForcingCheckOrdinal.forces_wellorderable hM hpre hp (args1 X) 0).mp hWo q hq hqp
  obtain ⟨rank,hRank⟩ := ForcingRawRank.exists_rank hM eta
  obtain ⟨s,hs,hsr,beta,hBeta,_hBound,checked,hChecked,hEq⟩ := ForcingOrdinalDecision.forces_ordinal_decide hM
    hpre htW hTop (fun x => domain_semantics env rho G F x) hCheck (args1 eta) 0 hEta hr hRank ho r hr (hpre.1 r hr)
  obtain ⟨t,ht,hts,J,hJ,hForce⟩ := hInj s hs hsr
  refine ⟨t,ht,hpre.2 t r q ht hr hq (hpre.2 t s r ht hs hr hts hsr) hrq,beta,hBeta,checked,hChecked,J,hJ,?_⟩
  apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.injection 0 1 2)
    (args3 J X eta) (args3 J X checked) t ht ?_).mp hForce
  intro j
  exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre J t ht)
    (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre X t ht)
      (Fin.cases (ForcingAtomicBasic.eq_mono hM hpre ht hts hEq) (fun i => Fin.elim0 i))) j

def witness {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P top X q : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let b : Fin k → Fin (m+4) := fun j => up (base j)
  let r := (Fin.last m).castSucc.castSucc.castSucc
  let beta := (Fin.last (m+1)).castSucc.castSucc
  let checked := (Fin.last (m+2)).castSucc
  let J := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((Formula.mem r (up P)).conj
    ((ReplacementPredicates.rel L b r (up q)).conj
      ((OrdinalSyntax.ordinal beta).conj ((ForcingCheckName.checkName (up top) beta checked).conj
        ((MinimalPredicates.pred H b J).conj
          (ForcingFormula.formula L H b (args3 J (up X) checked) (up P) r (Source.SetLanguage.injection 0 1 2))))))))))

theorem witness_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P top X q : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (witness L H base P top X q) ↔
      Witness L H (fun j => v (base j)) (v P) (v top) (v X) (v q) := by
  simp only [witness,Witness,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingRawRank.ordinal_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingFormula.formula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  have hV (r beta checked J : M.Carrier .set) :
      (fun j => Fin.lastCases J (Fin.lastCases checked (Fin.lastCases beta (Fin.lastCases r v)))
        (args3 (Fin.last (m+3)) X.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc j)) =
          args3 J (v X) checked := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
    · change Fin.lastCases J (Fin.lastCases checked (Fin.lastCases beta (Fin.lastCases r v)))
        (Fin.last (m+3)) = J
      rw [Fin.lastCases_last]
    · change Fin.lastCases J (Fin.lastCases checked (Fin.lastCases beta (Fin.lastCases r v)))
        X.castSucc.castSucc.castSucc.castSucc = v X
      rw [Fin.lastCases_castSucc,Fin.lastCases_castSucc,Fin.lastCases_castSucc,Fin.lastCases_castSucc]
    · change Fin.lastCases J (Fin.lastCases checked (Fin.lastCases beta (Fin.lastCases r v)))
        (Fin.last (m+2)).castSucc = checked
      rw [Fin.lastCases_castSucc,Fin.lastCases_last]
  constructor
  · rintro ⟨r,beta,checked,J,hr,hrq,hBeta,hChecked,hJ,hForce⟩
    rw [hV] at hForce
    exact ⟨r,hr,hrq,beta,hBeta,checked,hChecked,J,hJ,hForce⟩
  · rintro ⟨r,hr,hrq,beta,hBeta,checked,hChecked,J,hJ,hForce⟩
    refine ⟨r,beta,checked,J,hr,hrq,hBeta,hChecked,hJ,?_⟩
    rw [hV]
    exact hForce

def denseChecked {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P top X p : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel L (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (witness L H (fun j => (base j).castSucc) P.castSucc top.castSucc X.castSucc (Fin.last m))))

theorem denseChecked_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P top X p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (denseChecked L H base P top X p) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (v P) → MapRel L (fun j => v (base j)) q (v p) →
        Witness L H (fun j => v (base j)) (v P) (v top) (v X) q := by
  simp only [denseChecked,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),witness_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args1 X) (rho 6) p (ForcingCheckOrdinal.wellorderable 0))].foldr Definitional.Formula.imp
          (ProjectSyntax.encode id (denseChecked (orderFormula (rho 0) mul) (domain rho G F) id (rho 6) top X p)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F mul top X p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingFormula.formula_semantics,denseChecked_semantics,id_eq]
  intro hPres hG hF ht hpre hp hWo
  have hV : (fun j => env (args1 X j)) = args1 (env X) := by
    funext j
    exact Fin.cases rfl (fun i => Fin.elim0 i) j
  apply wellorderable_check_dense hM env rho I K B w G F mul top hPres hG hF ht hpre hp
  rw [hV] at hWo
  exact hWo

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F mul top X p)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul top X p hM)

-- Retain the existing native injection eliminator verbatim; see SOURCE_LOCK.
private theorem injection_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q f X Y x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2))
    (hx : ForcingClassEvaluation.Predicate H env x) (hy : ForcingClassEvaluation.Predicate H env y)
    (hz : ForcingClassEvaluation.Predicate H env z)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hxX : Forces false R env P x X q) (hyX : Forces false R env P y X q)
    (hxz : Force R H env (args3 f x z) P q (Source.SetLanguage.edge 0 1 2))
    (hyz : Force R H env (args3 f y z) P q (Source.SetLanguage.edge 0 1 2)) :
    Forces true R env P x y q := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 x hx
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh z hz
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq) hyX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq)
    ⟨(ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 3 5).mpr hxz,
      (ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 4 5).mpr hyz⟩
  exact hh

/-- Source formula retained exactly; parameters f,X,Y,J,i,x. -/
def indexedSection : Formula 6 :=
  .all ((Formula.mem 6 2).imp ((Source.SetLanguage.edge 3 6 4).imp
    ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6))))

theorem forces_indexedSection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (f X Y J i x : M.Carrier .set) :
    Force L H env (Fin.lastCases x (ForcingMapCalculus.five f X Y J i)) P p indexedSection ↔
      ∀ y, Predicate H env y → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p →
        Forces false L env P y Y q → ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel L env r q →
          Force L H env (args3 J y i) P r (Source.SetLanguage.edge 0 1 2) →
            Forces false L env P x X r ∧ Force L H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
  let v : Fin 6 → M.Carrier .set := Fin.lastCases x (ForcingMapCalculus.five f X Y J i)
  let body : Formula 7 := (Formula.mem 6 2).imp ((Source.SetLanguage.edge 3 6 4).imp
    ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6)))
  let vv (y : M.Carrier .set) : Fin 7 → M.Carrier .set := Fin.lastCases y v
  have e0 (y : M.Carrier .set) : vv y (0 : Fin 7) = f := rfl
  have e3 (y : M.Carrier .set) : vv y (3 : Fin 7) = J := rfl
  have e4 (y : M.Carrier .set) : vv y (4 : Fin 7) = i := rfl
  have e5 (y : M.Carrier .set) : vv y (5 : Fin 7) = x := rfl
  have e6 (y : M.Carrier .set) : vv y (6 : Fin 7) = y := rfl
  have hJE (y r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) :
      Force L H env (vv y) P r (Source.SetLanguage.edge 3 6 4) ↔
        Force L H env (args3 J y i) P r (Source.SetLanguage.edge 0 1 2) := by
    have he := ForcingRelationClass.edge_formula hM (H := H) hpre hr (vv y) (3 : Fin 7) 6 4
    rw [e3,e6,e4] at he
    exact he
  have hFE (y r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) :
      Force L H env (vv y) P r (Source.SetLanguage.edge 0 5 6) ↔
        Force L H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
    have he := ForcingRelationClass.edge_formula hM (H := H) hpre hr (vv y) (0 : Fin 7) 5 6
    rw [e0,e5,e6] at he
    exact he
  change Force L H env v P p (.all body) ↔ _
  rw [ForcingFormula.force_all hM (H := H) hpre hp v body]
  constructor
  · intro h y hy q hq hqp hMY r hr hrq hJi
    have h1 := (ForcingFormula.force_imp hM (H := H) hpre hp (vv y) (Formula.mem 6 2)
      ((Source.SetLanguage.edge 3 6 4).imp ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6)))).mp
        (h y hy) q hq hqp hMY
    have h2 := (ForcingFormula.force_imp hM (H := H) hpre hq (vv y) (Source.SetLanguage.edge 3 6 4)
      ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6))).mp h1 r hr hrq ((hJE y r hr).mpr hJi)
    exact ⟨h2.1,(hFE y r hr).mp h2.2⟩
  · intro h y hy
    apply (ForcingFormula.force_imp hM (H := H) hpre hp (vv y) (Formula.mem 6 2)
      ((Source.SetLanguage.edge 3 6 4).imp ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6)))).mpr
    intro q hq hqp hMY
    apply (ForcingFormula.force_imp hM (H := H) hpre hq (vv y) (Source.SetLanguage.edge 3 6 4)
      ((Formula.mem 5 1).conj (Source.SetLanguage.edge 0 5 6))).mpr
    intro r hr hrq hJi
    have h2 := h y hy q hq hqp hMY r hr hrq ((hJE y r hr).mp hJi)
    exact ⟨h2.1,(hFE y r hr).mpr h2.2⟩

/-- Source's single-fiber two-case proof. Empty is only a local generic
helper input; the actual object endpoint below discharges it with the
ALREADY AVAILABLE HS empty-name theorem. No family of defaults is chosen. -/
theorem indexedSection_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (f X Y J O i empty : M.Carrier .set)
    (hi : Predicate H env i) (hEmpty : Predicate H env empty)
    (hf : Force L H env (args3 f X Y) P p (Source.SetLanguage.surjection 0 1 2))
    (hJ : Force L H env (args3 J Y O) P p (Source.SetLanguage.injection 0 1 2)) :
    Force L H env (ForcingMapCalculus.five f X Y J i) P p (.ex indexedSection) := by
  apply (ForcingFormula.force_ex L H env _ P p _).mpr
  intro q hq hqp
  by_cases h : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧
      ∃ y, Predicate H env y ∧ Forces false L env P y Y r ∧
        Force L H env (args3 J y i) P r (Source.SetLanguage.edge 0 1 2)
  · obtain ⟨r,hr,hrq,y,hy,hMY,hyi⟩ := h
    obtain ⟨s,hs,hsr,x,hx,hMX,hxy⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hf hy
      hr (hpre.2 r q p hr hq hp hrq hqp) hMY hr (hpre.1 r hr)
    refine ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,x,hx,?_⟩
    apply (forces_indexedSection hM hpre hs f X Y J i x).mpr
    intro z hz t ht hts hMZ a ha hat hzi
    have has := hpre.2 a t s ha ht hs hat hts
    have har := hpre.2 a s r ha hs hr has hsr
    have hap := hpre.2 a r p ha hr hp har (hpre.2 r q p hr hq hp hrq hqp)
    have hzy := injection_one hM hpre hp hJ hz hy hi ha hap
      (ForcingAtomicBasic.mem_mono hM hpre ha hat hMZ)
      (ForcingAtomicBasic.mem_mono hM hpre ha har hMY) hzi
      (ForcingFormula.mono hM hpre _ _ hr ha har hyi)
    refine ⟨ForcingAtomicBasic.mem_mono hM hpre ha has hMX,?_⟩
    apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.edge 0 1 2)
      (args3 f x z) (args3 f x y) a ha ?_).mpr (ForcingFormula.mono hM hpre _ _ hs ha has hxy)
    intro j
    exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre f a ha)
      (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre x a ha) (Fin.cases hzy (fun n => Fin.elim0 n))) j
  · refine ⟨q,hq,hpre.1 q hq,empty,hEmpty,?_⟩
    apply (forces_indexedSection hM hpre hq f X Y J i empty).mpr
    intro y hy r hr hrq hMY s hs hsr hJi
    exact (h ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,y,hy,
      ForcingAtomicBasic.mem_mono hM hpre hs hsr hMY,hJi⟩).elim

/-- Source single-fiber existence in the actual product system. The HS
empty name is constructed from existing empty/action/normal-filter proofs. -/
def sectionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul top f X Y J O i p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F i),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 J Y O) (rho 6) p (Source.SetLanguage.injection 0 1 2))].foldr Definitional.Formula.imp
          (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
            (ForcingMapCalculus.five f X Y J i) (rho 6) p (.ex indexedSection))))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem section_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y J O i p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sectionSentence rho I K B w G F mul top f X Y J O i p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,ForcingFormula.formula_semantics,id_eq]
  intro hPres hG hF ht hpre hi hp hf hJ
  have h3 (a b c : Fin k) : (fun j => env (args3 a b c j)) = args3 (env a) (env b) (env c) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n))) j
  have h5 : (fun j => env (ForcingMapCalculus.five f X Y J i j)) =
      ForcingMapCalculus.five (env f) (env X) (env Y) (env J) (env i) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n))))) j
  rw [h3 f X Y] at hf
  rw [h3 J Y O] at hJ
  rw [h5]
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have hActions := ForcingProductFamily.family hM v7 hPres hG
  have hEmpty := ForcingHS.empty_hs hM actionFormula v7 (env G) (env (rho 6)) (env F) (env top) (by
    intro pi hpi
    obtain ⟨act,hAct⟩ := hActions.1 pi hpi
    exact ⟨act,hAct,(hActions.2 pi act hpi hAct).1⟩) hF.1 ht
  exact indexedSection_exists hM hpre hp (env f) (env X) (env Y) (env J) (env O) (env i) (env top)
    ((domain_semantics env rho G F (env i)).mpr hi)
    ((domain_semantics env rho G F (env top)).mpr hEmpty) hf hJ

theorem section_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y J O i p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (sectionSentence rho I K B w G F mul top f X Y J O i p)) :=
  ModelTransfer.derives (fun _ hM => section_models rho I K B w G F mul top f X Y J O i p hM)

end PPAC.Migration.ForcingOrderedSections
