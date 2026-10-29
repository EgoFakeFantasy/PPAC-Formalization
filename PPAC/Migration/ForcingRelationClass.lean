/- Pinned LocalRecords.relationClass, mem_relationClass, relationClass_bounded,
relationClass_congr and forces_classOf/isClass (299-389).
The class is the existing separated HS name, in the original pure language.
Consumers: localLabelClass and AvailableRecords.classRepresentationSet_denseBelow. -/
import PPAC.Migration.ForcingEligibility
import PPAC.Migration.ForcingLocalNormalize

namespace PPAC.Migration.ForcingRelationClass
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSeparation (Separated)
open ForcingPowerName (Bound Subset)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u v w
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem comp_args2 {α : Type v} {β : Type w} (v : α → β) (a b : α) :
    (fun i => v (args2 a b i)) = args2 (v a) (v b) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i) i

private theorem comp_args3 {α : Type v} {β : Type w} (f : α → β) (a b c : α) :
    (fun i => f (args3 a b c i)) = args3 (f a) (f b) (f c) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i) i) i

private theorem snoc_args2 (a b c : M.Carrier .set) :
    Fin.lastCases c (args2 a b) = args3 a b c := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i) i) i

/-- Exact separated-edge definition; no equivalence-relation premise. -/
def Class {k : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (P A E x name : M.Carrier .set) : Prop :=
  Separated R H env (args2 E x) P A name (Source.SetLanguage.edge 0 1 2)

def relationClass {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (rr : Fin k → Fin m) (P A E x name : Fin m) : Formula m :=
  ForcingSeparation.separated R H rr (args2 E x) P A name (Source.SetLanguage.edge 0 1 2)

theorem relationClass_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rr : Fin k → Fin m) (P A E x name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (relationClass R H rr P A E x name) ↔
      Class R H (fun j => env (rr j)) (env P) (env A) (env E) (env x) (env name) := by
  simp only [relationClass,Class,ForcingSeparation.separated_semantics (M := M),comp_args2]

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w A E x : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) A)
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) E)
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) A E x name := by
  exact ForcingSeparationAxiom.exists_at_values hM env rho G F mul hp hG hF hA (args2 E x)
    (fun i => Fin.cases hE (fun i => Fin.cases hx (fun j => Fin.elim0 j) i) i)
    (Source.SetLanguage.edge 0 1 2)

/-- Keep the source graph formula expanded, avoiding an assumed App relation. -/
theorem edge_formula (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (E x y : Fin n) :
    Force R H env v P p (Source.SetLanguage.edge E x y) ↔
      Force R H env (args3 (v E) (v x) (v y)) P p (Source.SetLanguage.edge 0 1 2) := by
  simp only [Source.SetLanguage.edge,ForcingSound.rename hM hpre _ _ _ _ hp]
  rfl

theorem mem_class (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A E x name y p : M.Carrier .set} (hpre : PreorderOn R env P)
    (hn : Class R H env P A E x name) (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P y name p ↔ Forces false R env P y A p ∧
      Force R H env (args3 E x y) P p (Source.SetLanguage.edge 0 1 2) := by
  simpa only [snoc_args2] using ForcingSeparationAxiom.mem_separate hM hpre hn hp (nu := y)

theorem bounded {k n : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {S : Formula (n+2)} {v : Fin n → M.Carrier .set}
    {G F P A E x name bound : M.Carrier .set} (hb : Bound P A bound)
    (hn : HS S v G P F name) (hc : Class R H env P A E x name) : Subset name bound := by
  intro z hz
  obtain ⟨child,p,hcode,hp,_⟩ := ForcingNames.edges (ForcingHS.isName hn) z hz
  obtain ⟨⟨c,he⟩,_,_,_⟩ := (hc child p).mp ⟨z,hcode,hz⟩
  exact (hb z).mpr ⟨child,c,he,p,hp,hcode⟩

theorem congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {S : Formula (n+2)} {v : Fin n → M.Carrier .set}
    {G F P A A' E E' x x' name name' p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hn : HS S v G P F name) (hn' : HS S v G P F name')
    (hc : Class R H env P A E x name) (hc' : Class R H env P A' E' x' name')
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hA : Forces true R env P A A' p) (hE : Forces true R env P E E' p)
    (hx : Forces true R env P x x' p) : Forces true R env P name name' p := by
  apply ForcingBasicSetAxioms.eq_of_same_members hM hpre hn hn' hp
  intro y _ q hq hqp
  rw [mem_class hM hpre hc hq,mem_class hM hpre hc' hq]
  refine and_congr (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp hA)) ?_
  apply ForcingFormula.tuple_congr hM hpre _ _ _ q hq
  intro i
  exact Fin.cases (ForcingAtomicBasic.eq_mono hM hpre hq hqp hE)
    (fun i => Fin.cases (ForcingAtomicBasic.eq_mono hM hpre hq hqp hx)
      (fun i => Fin.cases (ForcingAtomicBasic.eq_refl hM hpre y q hq) (fun j => Fin.elim0 j) i) i) i

theorem forces_classOf (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {p name : M.Carrier .set}
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (v : Fin n → M.Carrier .set) (tau A E x : Fin n)
    (ht : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v tau))
    (hn : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name)
    (hc : Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (v A) (v E) (v x) name) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p
      (ForcingEligibility.classOf tau A E x) ↔
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (v tau) name p := by
  simp only [ForcingEligibility.classOf,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingEligibility.classOfFormula,ForcingFormula.force_all hM hpre hp,Source.Formula.iff,
    ForcingFormula.force_conj,ForcingFormula.force_imp hM hpre hp,ForcingFormula.force_mem]
  constructor
  · intro h
    apply ForcingBasicSetAxioms.eq_of_same_members hM hpre ht hn hp
    intro y hy q hq hqp
    have hy' := (domain_semantics env rho G F y).mpr hy
    rw [mem_class hM hpre hc hq]
    have hEdge := edge_formula hM (H := domain rho G F) hpre hq
      (Fin.lastCases y (fun i => v (Fin.cases tau (args3 A E x) i))) (2 : Fin 5) 3 4
    constructor
    · intro hmem
      have hh := (h y hy').1 q hq hqp hmem
      exact ⟨hh.1,hEdge.mp hh.2⟩
    · rintro ⟨hm,he⟩
      exact (h y hy').2 q hq hqp ⟨hm,hEdge.mpr he⟩
  · intro he y _
    constructor
    · intro q hq hqp hm
      have hh := (mem_class hM hpre hc hq).mp
        ((ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mp hm)
      exact ⟨hh.1,(edge_formula hM hpre hq _ (2 : Fin 5) 3 4).mpr hh.2⟩
    · intro q hq hqp hh
      exact (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mpr
        ((mem_class hM hpre hc hq).mpr ⟨hh.1,(edge_formula hM hpre hq _ (2 : Fin 5) 3 4).mp hh.2⟩)

/-- Source forces_isClass, with the actual class witness and its HS proof.
All witnesses range over the internal universe, including nonstandard names. -/
theorem forces_isClass (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w p : M.Carrier .set}
    (hpresentation : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (v : Fin n → M.Carrier .set) (tau A E : Fin n)
    (ht : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v tau))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v A))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v E)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (ForcingEligibility.isClass tau A E) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env r q ∧
          ∃ x name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x ∧
            HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
            Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (v A) (v E) x name ∧
            Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (v A) r ∧
            Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (v tau) name r := by
  rw [ForcingEligibility.isClass,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingEligibility.isClassFormula,ForcingFormula.force_ex]
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hm,hclass⟩ := h q hq hqp
    have hx' := (domain_semantics env rho G F x).mp hx
    obtain ⟨name,hn,hc⟩ := exists_class hM env rho G F mul hpresentation hG hF hA hE hx'
    exact ⟨r,hr,hrq,x,name,hx',hn,hc,hm,
      (forces_classOf hM env rho G F mul hpre hr _ (0 : Fin 4) 1 2 3 ht hn hc).mp hclass⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,name,hx,hn,hc,hm,he⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,(domain_semantics env rho G F x).mpr hx,hm,
      (forces_classOf hM env rho G F mul hpre hr _ (0 : Fin 4) 1 2 3 ht hn hc).mpr he⟩

/-- The common-support constructor already used by localNormalize, now at
exactly the source relationClass formula. -/
theorem exists_supported (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul A E x : Fin k)
    {I K B w fixing bound : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hFix : ForcingConjugationGraph.Subgroup I (env G) fixing)
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env x))
    (hAf : ForcingSupportedNames.Supported (fun j => env (rho j)) fixing (env A))
    (hEf : ForcingSupportedNames.Supported (fun j => env (rho j)) fixing (env E))
    (hxf : ForcingSupportedNames.Supported (fun j => env (rho j)) fixing (env x))
    (hb : Bound (env (rho 6)) (env A) bound) :
    ∃ name, ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) bound fixing name ∧
      Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env E) (env x) name := by
  obtain ⟨name,hn,hc,hfixed⟩ := ForcingLocalNormalize.separate_supported hM env rho G F mul A hp hG hF hFix hA hAf
    (args2 E x) (fun i => Fin.cases hE (fun i => Fin.cases hx (fun j => Fin.elim0 j) i) i)
    (fun i => Fin.cases hEf (fun i => Fin.cases hxf (fun j => Fin.elim0 j) i) i) (Source.SetLanguage.edge 0 1 2)
  rw [comp_args2] at hc
  exact ⟨name,⟨⟨hn,bounded hb hn hc⟩,hfixed⟩,hc⟩

def result {k : Nat} (rho : Fin 7 → Fin k) (G F mul A E x bound : Fin k) : Formula k :=
  .ex ((ForcingHS.hs actionFormula (paramsUp rho) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
    ((relationClass (orderFormula (rho 0) mul) (domain rho G F) Fin.castSucc
      (rho 6).castSucc A.castSucc E.castSucc x.castSucc (Fin.last k)).conj
      (Source.SetLanguage.subset (Fin.last k) bound.castSucc)))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul A E x bound : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho G F mul A E x bound) ↔
      ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
        Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env E) (env x) name ∧
        Subset name (env bound) := by
  simp only [result,Formula.Realize,ForcingHS.hs_semantics (M := M),relationClass_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul A E x bound : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((ForcingHS.hs actionFormula rho G (rho 6) F A).imp
        ((ForcingHS.hs actionFormula rho G (rho 6) F E).imp
          ((ForcingHS.hs actionFormula rho G (rho 6) F x).imp
            ((ForcingLabelBound.bound (rho 6) A bound).imp (result rho G F mul A E x bound)))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul A E x bound : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w G F mul A E x bound)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env _
  simp only [Formula.Realize,ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingLabelBound.bound_semantics (M := M),result_semantics (M := M)]
  intro hp hG hF hA hE hx hb
  obtain ⟨name,hn,hc⟩ := exists_class hM env rho G F mul hp hG hF hA hE hx
  exact ⟨name,hn,hc,bounded hb hn hc⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul A E x bound : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w G F mul A E x bound)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w G F mul A E x bound hM)

def characterizationSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul tau A E x name p : Fin k) : Source.Sentence :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  ((ForcingAtomicBasic.preorder R id (rho 6)).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F tau).imp
      ((ForcingHS.hs actionFormula rho G (rho 6) F name).imp
        ((relationClass R H id (rho 6) A E x name).imp
          ((Formula.mem p (rho 6)).imp
            ((ForcingFormula.formula R H id id (rho 6) p (ForcingEligibility.classOf tau A E x)).iff
              (ForcingAtomicRelations.forces true R id (rho 6) tau name p))))))).close

theorem characterization_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul tau A E x name p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (characterizationSentence rho G F mul tau A E x name p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env _
  simp only [Formula.Realize,ForcingAtomicBasic.preorder_semantics (M := M),
    ForcingHS.hs_semantics (M := M),relationClass_semantics (M := M),ForcingFormula.formula_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M)]
  intro hpre ht hn hc hp
  have h := forces_classOf hM env rho G F mul hpre hp env tau A E x ht hn hc
  exact ⟨h.mp,h.mpr⟩

theorem characterization_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul tau A E x name p : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (characterizationSentence rho G F mul tau A E x name p)) :=
  ModelTransfer.derives (fun _ hM => characterization_models rho G F mul tau A E x name p hM)

/-- The internal dense representation formula used by AvailableRecords. -/
def denseClasses {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (rr : Fin k → Fin m) (rho : Fin 7 → Fin m) (G F P tau A E p : Fin m) : Formula m :=
  let up := fun j : Fin m => j.castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc
  let x := (Fin.last (m+2)).castSucc
  let name := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp rr) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (paramsUp (paramsUp rr)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (.ex (.ex ((ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up P) (up F) x).conj
            ((ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up P) (up F) name).conj
              ((relationClass R H (fun j => up (rr j)) (up P) (up A) (up E) x name).conj
                ((ForcingAtomicRelations.forces false R (fun j => up (rr j)) (up P) x (up A) r).conj
                  (ForcingAtomicRelations.forces true R (fun j => up (rr j)) (up P) (up tau) name r))))))))))))

theorem denseClasses_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F P tau A E p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (denseClasses R H rr rho G F P tau A E p) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R (fun j => env (rr j)) q (env p) →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R (fun j => env (rr j)) r q ∧
          ∃ x name, HS actionFormula (fun j => env (rho j)) (env G) (env P) (env F) x ∧
            HS actionFormula (fun j => env (rho j)) (env G) (env P) (env F) name ∧
            Class R H (fun j => env (rr j)) (env P) (env A) (env E) x name ∧
            Forces false R (fun j => env (rr j)) (env P) x (env A) r ∧
            Forces true R (fun j => env (rr j)) (env P) (env tau) name r := by
  simp only [denseClasses,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingHS.hs_semantics (M := M),relationClass_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def isClassSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul tau A E p : Fin k) : Source.Sentence :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((ForcingAtomicBasic.preorder R id (rho 6)).imp
        ((ForcingHS.hs actionFormula rho G (rho 6) F tau).imp
          ((ForcingHS.hs actionFormula rho G (rho 6) F A).imp
            ((ForcingHS.hs actionFormula rho G (rho 6) F E).imp
              ((Formula.mem p (rho 6)).imp
                ((ForcingFormula.formula R H id id (rho 6) p (ForcingEligibility.isClass tau A E)).iff
                  (denseClasses R H id rho G F (rho 6) tau A E p)))))))))).close

theorem isClass_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul tau A E p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (isClassSentence rho I K B w G F mul tau A E p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env _
  simp only [Formula.Realize,ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingAtomicBasic.preorder_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),denseClasses_semantics (M := M)]
  intro hpres hG hF hpre ht hA hE hp
  have h := forces_isClass hM env rho G F mul hpres hG hF hpre hp env tau A E ht hA hE
  exact ⟨h.mp,h.mpr⟩

theorem isClass_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul tau A E p : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (isClassSentence rho I K B w G F mul tau A E p)) :=
  ModelTransfer.derives (fun _ hM => isClass_models rho I K B w G F mul tau A E p hM)

/-- Literal labelClass/localLabelClass, reusing the actual label name and
labelSet. Support and forced membership are proved, not supplied as oracles. -/
theorem actual_labelClass (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul A E x : Fin k)
    {I K B w mu c t b j J fixing bound e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hA : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b (env A))
    (hx : ForcingLabelNames.Label (env (rho 6)) K c t j b (env x))
    (hb : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b bound)
    (hJI : Subset J I) (hFix : ForcingLabelPermutations.Fixing (env G) J fixing)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hEf : ForcingSupportedNames.Supported (fun j => env (rho j)) fixing (env E)) :
    ∃ name, ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) bound fixing name ∧
      Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env E) (env x) name ∧
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 name (env A) (env E))
          (env (rho 6)) p (ForcingEligibility.isClass 0 1 2) := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSub := ForcingConjugationGraph.fixing_subgroup hM hG hFix hJI
  have hSmall := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  obtain ⟨hAHS,hAf⟩ := ForcingLabelSet.HS_and_fixed hM (fun i => env (rho i)) hpres hG hNormal hF hw hSmall hc ht hA
  have hxHS := ForcingLabelNames.label_HS hM (fun i => env (rho i)) hpres hG hNormal hF hw hSmall hc ht (hJI j hj) hx
  have hxf : ForcingSupportedNames.Supported (fun i => env (rho i)) fixing (env x) := by
    intro pi hpi a ha
    obtain ⟨hpiG,hpiJ⟩ := (hFix pi).mp hpi
    exact ForcingLabelNames.label_move hM (fun i => env (rho i)) hpres ht ((hG pi).mp hpiG)
      ((ForcingProductFamily.mapRel_action _ _ _).mp ha) (hpiJ j hj) hx hx
  obtain ⟨name,hn,hclass⟩ := exists_supported hM env rho G F mul A E x hpres hG hNormal hSub hAHS hE hxHS
    (fun pi hpi a ha => hAf pi (hSub.1 pi hpi) a ha) hEf hxf ((ForcingLabelBound.bound_iff hM hA).mpr hb)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  refine ⟨name,hn,hclass,?_⟩
  intro p hp
  apply (forces_isClass hM env rho G F mul hpres hG hNormal hpre hp (args3 name (env A) (env E))
    0 1 2 hn.1.1 hAHS hE).mpr
  intro q hq _
  have htW := (hpres.2.2.2.2.2 t).mpr (Or.inl ht)
  have hqt := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul q t).mpr (Or.inl ht)
  have hmem := ForcingAtomicBasic.mem_of_edge_eq hM hpre htW hqt
    ((ForcingLabelSet.edge_labelSet hM hA (env x) t).mpr ⟨rfl,j,hJI j hj,hx⟩)
    (ForcingAtomicBasic.eq_refl hM hpre (env x) q hq)
  exact ⟨q,hq,hpre.1 q hq,env x,name,hxHS,hn.1.1,hclass,hmem,ForcingAtomicBasic.eq_refl hM hpre name q hq⟩

def localResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul A E x bound fixing : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  .ex ((ForcingLocalNames.localName (paramsUp rho) G.castSucc F.castSucc bound.castSucc fixing.castSucc (Fin.last k)).conj
    ((relationClass R H Fin.castSucc (rho 6).castSucc A.castSucc E.castSucc x.castSucc (Fin.last k)).conj
      (.all ((Formula.mem (Fin.last (k+1)) (rho 6).castSucc.castSucc).imp
        (ForcingFormula.formula R H (fun j => j.castSucc.castSucc)
          (args3 (Fin.last k).castSucc A.castSucc.castSucc E.castSucc.castSucc)
          (rho 6).castSucc.castSucc (Fin.last (k+1)) (ForcingEligibility.isClass 0 1 2))))))

theorem localResult_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul A E x bound fixing : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (localResult rho G F mul A E x bound fixing) ↔
      ∃ name, ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env fixing) name ∧
        Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env E) (env x) name ∧
        ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
          Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 name (env A) (env E)) (env (rho 6)) p
            (ForcingEligibility.isClass 0 1 2) := by
  simp only [localResult,Formula.Realize,ForcingLocalNames.localName_semantics (M := M),
    relationClass_semantics (M := M),ForcingFormula.formula_semantics (M := M),comp_args3,
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def localSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b j J fixing bound e G F mul A E x : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b A))
      (.imp (ProjectSyntax.encode id (ForcingLabelNames.label (rho 6) K c t j b x))
      (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b bound))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset J I))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G J fixing))
      (.imp (ProjectSyntax.encode id (Source.Formula.mem j J))
      (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing E))
      (ProjectSyntax.encode id (localResult rho G F mul A E x bound fixing))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed]

theorem local_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b j J fixing bound e G F mul A E x : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (localSentence rho I K B w mu c t b j J fixing bound e G F mul A E x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (localSentence rho I K B w mu c t b j J fixing bound e G F mul A E x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),localResult_semantics (M := M),
    Source.Formula.Realize,Project.Term.eval_bound]
  exact fun hw hMu hm hp hG hF hc ht hA hx hb hJI hFix hj hE hEf =>
    actual_labelClass hM env rho G F mul A E x hw hMu hm hp hG hF hc ht hA hx hb hJI hFix hj hE hEf

theorem local_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b j J fixing bound e G F mul A E x : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (localSentence rho I K B w mu c t b j J fixing bound e G F mul A E x)) :=
  ModelTransfer.derives (fun _ hM => local_models rho I K B w mu c t b j J fixing bound e G F mul A E x hM)

end PPAC.Migration.ForcingRelationClass
