/- Pinned SliceAssembly.falseRelation/empty_domain_injection/
empty_domain_wellorderable/nonwellorderable_member_dense:16-55.
Consumers: SliceAssembly.slice_candidate and presentation_reverse_injection.
Reuse actual graph construction, checked ordinals and the original forcing
front end. Only one member below one condition, never a default family. -/
import PPAC.Migration.ForcingSliceCoverage

namespace PPAC.Migration.ForcingEmptyDomain
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingRelationGraphForcing (Holds)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem args2_map {a : Type v} {b : Type u} (g : a → b) (X Y : a) :
    (fun j => g (args2 X Y j)) = args2 (g X) (g Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) j

private theorem args3_map {a : Type v} {b : Type u} (g : a → b) (f X Y : a) :
    (fun j => g (args3 f X Y j)) = args3 (g f) (g X) (g Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- Same source empty relation, represented by the existing formula relation. -/
def falseRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul X Y : Fin k) : Formula (k+3) :=
  ForcingMapCalculus.relationOf rho G F mul (args2 X Y) (.bot : Formula 4)

theorem falseRelation_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X Y : Fin k) (p x y : M.Carrier .set) :
    Holds (falseRelation rho G F mul X Y) env p x y ↔ False := by
  rw [falseRelation,ForcingMapCalculus.relationOf_semantics]
  rfl

/-- Exactly source emptiness on the full HS name domain, below p. -/
def Empty {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X : Fin k) (p : M.Carrier .set) : Prop :=
  ∀ x, Predicate (domain rho G F) env x → ∀ q,
    (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
    MapRel (orderFormula (rho 0) mul) env q p →
    ¬ Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) q

/-- The actual common support and empty graph are constructor OUTPUTS. -/
theorem empty_domain_injection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top X Y : Fin k)
    {p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hEmpty : Empty env rho G F mul X p) :
    ∃ graph, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env X) (env Y))
        (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) := by
  obtain ⟨S,graph,_hS,_hSF,_hTuple,hGraph,hGraphHS,_hGraphFix⟩ :=
    ForcingMapCalculus.actual_reuse hM env rho I K B w G F mul top (args2 X Y) (.bot : Formula 4) 0 (Fin.succ (0 : Fin 1))
      hPres hG hF ht (fun j => Fin.cases hX (Fin.cases hY (fun t => Fin.elim0 t)) j)
  let ext : Fin (k+1) → M.Carrier .set := Fin.cases S env
  let rr : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  let ns : Fin 2 → Fin (k+1) := args2 X.succ Y.succ
  let R := orderFormula (rr 0) mul.succ
  let H := domain rr G.succ F.succ
  let Q := falseRelation rr G.succ F.succ mul.succ X.succ Y.succ
  have eu (a : Fin k) : ext a.succ = env a := rfl
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔ MapRel R ext a b := by
    simp only [orderFormula_semantics,R,rr,eu]
  have hH (x : M.Carrier .set) : Predicate (domain rho G F) env x ↔ Predicate H ext x := by
    simp only [domain_semantics,H,rr,eu]
  have hpre' : ForcingAtomicBasic.PreorderOn R ext (ext (rr 6)) := by
    simpa only [ForcingAtomicBasic.PreorderOn,rr,eu,← hR] using hpre
  have hX' : HS actionFormula (fun j => ext (rr j)) (ext G.succ) (ext (rr 6)) (ext F.succ) (ext X.succ) := by
    simpa only [rr,eu] using hX
  have hY' : HS actionFormula (fun j => ext (rr j)) (ext G.succ) (ext (rr 6)) (ext F.succ) (ext Y.succ) := by
    simpa only [rr,eu] using hY
  have hGraph' : ForcingRelationGraph.Graph R Q ext (rr 6) top.succ X.succ Y.succ graph := by
    have hNs := args2_map (fun a : Fin k => a.succ) X Y
    rw [hNs] at hGraph
    simpa only [R,Q,falseRelation,rr,ext,args2,args1,Fin.cases_zero,Fin.cases_succ] using hGraph
  have hForce : Force R H ext (args3 graph (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) := by
    apply ForcingRelationGraphFunctions.graph_injection hM ext rr G.succ F.succ mul.succ top.succ X.succ Y.succ Q
      (args3 graph (env X) (env Y)) 0 1 2 (by simpa only [rr,eu] using hPres)
      (by simpa only [eu] using hG) (by simpa only [eu] using hF) (by simpa only [eu] using ht)
      hpre' hX' hY'
      (ForcingMapCalculus.monotone hM ext rr G.succ F.succ mul.succ ns (.bot : Formula 4) hpre')
      (ForcingMapCalculus.congruent hM ext rr G.succ F.succ mul.succ ns (.bot : Formula 4) hpre')
      (ForcingMapCalculus.regular hM ext rr G.succ F.succ mul.succ ns (.bot : Formula 4) hpre') hGraph' rfl rfl ?_ ?_ ?_ hp
    · intro x hx q hq hqp hxX
      apply False.elim
      apply hEmpty x ((hH x).mpr ((domain_semantics ext rr G.succ F.succ x).mpr
        ((ForcingRelationGraphApplication.hs_actionAt ext rr _ _ _ _).mp hx))) q hq ((hR q p).mpr hqp)
      exact (ForcingSeparation.atomic_congr hR false (env (rho 6)) x (env X) q).mpr hxX
    · intro q _ _ x y z _ _ _ hRel _
      exact ((falseRelation_semantics ext rr G.succ F.succ mul.succ X.succ Y.succ q x y).mp hRel).elim
    · intro q _ _ x y z _ _ _ hRel _
      exact ((falseRelation_semantics ext rr G.succ F.succ mul.succ X.succ Y.succ q x z).mp hRel).elim
  exact ⟨graph,hGraphHS,(ForcingSeparation.force_congr hR hH (Source.SetLanguage.injection 0 1 2)
    (args3 graph (env X) (env Y)) (env (rho 6)) p).mpr hForce⟩

/-- No ordinal witness is supplied: reuse the existing empty-ordinal native
certificate, actual check constructor and the already completed injection law. -/
theorem empty_domain_wellorderable (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top X : Fin k)
    {p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hEmpty : Empty env rho G F mul X p) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 (env X))
      (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0) := by
  have hZero := (Translation.realizes_sentence M _).mp (ObjectOrdinalBasic.native_existsEmpty.semantically_entails M hM)
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem Fin.elim0 (ObjectOrdinalBasic.emptyOrdinalExists 0) at hZero
  simp only [ObjectOrdinalBasic.emptyOrdinalExists,Formula.Realize,ForcingRawRank.ordinal_semantics,
    Fin.lastCases_last] at hZero
  obtain ⟨zero,_hz,hOrd⟩ := hZero
  obtain ⟨checked,hChecked⟩ := ForcingCheckName.exists_checked hM (env top) zero
  have hCheckedHS := ForcingSectionInjection.checked_hs hM (fun j => env (rho j)) hPres hG hF ht hChecked
  let ext : Fin (k+1) → M.Carrier .set := Fin.cases checked env
  let rr : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have eu (a : Fin k) : ext a.succ = env a := rfl
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
      MapRel (orderFormula (rr 0) mul.succ) ext a b := by simp only [orderFormula_semantics,rr,eu]
  have hH (x : M.Carrier .set) : Predicate (domain rho G F) env x ↔ Predicate (domain rr G.succ F.succ) ext x := by
    simp only [domain_semantics,rr,eu]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (rr 0) mul.succ) ext (ext (rr 6)) := by
    simpa only [ForcingAtomicBasic.PreorderOn,rr,eu,← hR] using hpre
  have hEmpty' : Empty ext rr G.succ F.succ mul.succ X.succ p := by
    intro x hx q hq hqp hxX
    exact hEmpty x ((hH x).mpr hx) q hq ((hR q p).mpr hqp)
      ((ForcingSeparation.atomic_congr hR false (env (rho 6)) x (env X) q).mpr hxX)
  obtain ⟨graph,hGraphHS,hInj⟩ := empty_domain_injection hM ext rr I.succ K.succ B.succ w.succ G.succ F.succ mul.succ top.succ X.succ 0
    (by simpa only [rr,eu] using hPres) (by simpa only [eu] using hG) (by simpa only [eu] using hF)
    (by simpa only [eu] using ht) hpre' (by simpa only [rr,eu] using hX)
    (by simpa only [rr,eu,ext,Fin.cases_zero] using hCheckedHS) hp hEmpty'
  have hInj' : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env X) checked)
      (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) :=
    (ForcingSeparation.force_congr hR hH (Source.SetLanguage.injection 0 1 2)
      (args3 graph (env X) checked) (env (rho 6)) p).mpr hInj
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  apply ForcingCheckOrdinal.wellorderable_of_check_injection hM hpre htW hTop ?_ hp hOrd hChecked
    ((domain_semantics env rho G F checked).mpr hCheckedHS) ?_ hInj'
  · intro nu hnu chi c hedge
    exact (domain_semantics env rho G F chi).mpr (ForcingHS.child ((domain_semantics env rho G F nu).mp hnu) hedge)
  · apply (domain_semantics env rho G F graph).mpr
    simpa only [rr,eu] using hGraphHS

/-- Exactly one actual HS member below one condition. No simultaneous choice
of defaults, wellorders, quotient maps or family of names is involved. -/
theorem nonwellorderable_member_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top X : Fin k)
    {p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hNonWO : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 (env X))
      (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env r q ∧ ∃ x, Predicate (domain rho G F) env x ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) r := by
  intro q hq hqp
  apply Classical.byContradiction
  intro hn
  have he : Empty env rho G F mul X q := by
    intro x hx r hr hrq hMem
    exact hn ⟨r,hr,hrq,x,hx,hMem⟩
  exact (ForcingFormula.force_neg hM hpre hp (args1 (env X)) (ForcingCheckOrdinal.wellorderable 0)).mp hNonWO q hq hqp
    (empty_domain_wellorderable hM env rho I K B w G F mul top X hPres hG hF ht hpre hX hq he)

theorem nonwellorderable_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top X : Fin k)
    {p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hNonWO : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 (env X))
      (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0).neg) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 (env X))
      (env (rho 6)) p (Source.SetLanguage.nonempty 0) := by
  have hd := nonwellorderable_member_dense hM env rho I K B w G F mul top X hPres hG hF ht hpre hX hp hNonWO
  unfold Source.SetLanguage.nonempty
  rw [ForcingSound.rename hM hpre _ _ _ _ hp]
  apply (ForcingFormula.force_ex _ _ _ _ _ _ _).mpr
  intro q hq hqp
  obtain ⟨r,hr,hrq,x,hx,hMem⟩ := hd q hq hqp
  exact ⟨r,hr,hrq,x,hx,hMem⟩


def emptyFormula {k : Nat} (rho : Fin 7 → Fin k) (G F mul X p : Fin k) : Formula k :=
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let x := (Fin.last k).castSucc
  let q := Fin.last (k+1)
  .all ((MinimalPredicates.pred (domain rho G F) Fin.castSucc (Fin.last k)).imp
    (.all ((Formula.mem q (b (rho 6))).imp
      ((ReplacementPredicates.rel (orderFormula (rho 0) mul) b q (b p)).imp
        (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) b (b (rho 6)) x (b X) q).neg))))

theorem emptyFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (emptyFormula rho G F mul X p) ↔
      Empty env rho G F mul X (env p) := by
  simp only [emptyFormula,Empty,Source.Formula.neg,Formula.Realize,
    ForcingClassEvaluation.predicate_semantics,ForcingMapConditions.rel_semantics,ForcingAtomicRelations.forces_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def injectionResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul X Y p : Fin k) : Formula k :=
  .ex ((ForcingHS.hs actionFormula (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
    (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) Fin.castSucc
      (args3 (Fin.last k) X.castSucc Y.castSucc) (rho 6).castSucc p.castSucc (Source.SetLanguage.injection 0 1 2)))

theorem injectionResult_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X Y p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (injectionResult rho G F mul X Y p) ↔
      ∃ graph, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env X) (env Y))
          (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2) := by
  simp only [injectionResult,Formula.Realize,ForcingHS.hs_semantics,ForcingFormula.formula_semantics,args3_map,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl


def injectionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X Y p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (emptyFormula rho G F mul X p)].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (injectionResult rho G F mul X Y p)))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem injection_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (injectionSentence rho I K B w G F mul top X Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,
    emptyFormula_semantics,injectionResult_semantics,id_eq]
  exact empty_domain_injection hM env rho I K B w G F mul top X Y

theorem injection_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (injectionSentence rho I K B w G F mul top X Y p)) :=
  ModelTransfer.derives (fun _ hM => injection_models rho I K B w G F mul top X Y p hM)

def emptySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      .mem (.bound p) (.bound (rho 6))].foldr Definitional.Formula.imp
      (.conj (.imp (ProjectSyntax.encode id (emptyFormula rho G F mul X p)) (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args1 X) (rho 6) p (ForcingCheckOrdinal.wellorderable 0))))
        (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args1 X) (rho 6) p ((ForcingCheckOrdinal.wellorderable 0).neg))) (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args1 X) (rho 6) p (Source.SetLanguage.nonempty 0))))))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem empty_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (emptySentence rho I K B w G F mul top X p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,ForcingFormula.formula_semantics,
    emptyFormula_semantics,id_eq]
  intro hPres hG hF ht hpre hX hp
  exact ⟨empty_domain_wellorderable hM env rho I K B w G F mul top X hPres hG hF ht hpre hX hp,
    nonwellorderable_nonempty hM env rho I K B w G F mul top X hPres hG hF ht hpre hX hp⟩

theorem empty_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top X p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (emptySentence rho I K B w G F mul top X p)) :=
  ModelTransfer.derives (fun _ hM => empty_models rho I K B w G F mul top X p hM)

end PPAC.Migration.ForcingEmptyDomain
