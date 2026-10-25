/- Pinned ForcingNames.ConditionAction.Name.HS / hs_iff / empty_HS.
Internal closed-set witnesses replace the source external WellFounded.fix.
Their existence uses existing native Collection, Separation, Union and Insert.
Symmetry is literal stabilizer membership from ForcingStabilizer, not a parameter
standing for an assumed hereditary-symmetry theorem. -/
import PPAC.Migration.ForcingStabilizer
import YesMetaZFC.SetTheory.Collection

namespace PPAC.Migration.ForcingHS
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingStabilizer (Symmetric symmetric)
open ForcingMapConditions (MapRel)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def closed {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m)
    (G P F S : Fin m) : Formula m :=
  (ForcingNames.closed P S).conj (.all ((Formula.mem (Fin.last m) S.castSucc).imp
    (symmetric A (paramsUp rho) G.castSucc P.castSucc F.castSucc (Fin.last m))))

def Closed {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P F S : M.Carrier .set) : Prop :=
  ForcingNames.Closed P S ∧ ∀ sigma, (Definitional.Project.FirstOrderSemantics.reduct M).mem sigma S →
    Symmetric A params G P F sigma

def hs {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m)
    (G P F sigma : Fin m) : Formula m :=
  .ex ((Formula.mem sigma.castSucc (Fin.last m)).conj
    (closed A (paramsUp rho) G.castSucc P.castSucc F.castSucc (Fin.last m)))

def HS {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P F sigma : M.Carrier .set) : Prop :=
  ∃ S, (Definitional.Project.FirstOrderSemantics.reduct M).mem sigma S ∧ Closed A params G P F S

theorem closed_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (closed A rho G P F S) ↔
      Closed A (fun i => env (rho i)) (env G) (env P) (env F) (env S) := by
  simp only [closed,Closed,Formula.Realize,ForcingNames.closed_semantics (M := M),
    ForcingStabilizer.symmetric_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem hs_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (hs A rho G P F sigma) ↔
      HS A (fun i => env (rho i)) (env G) (env P) (env F) (env sigma) := by
  simp only [hs,HS,Formula.Realize,closed_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem isName {k : Nat} {A : Formula (k+2)} {params : Fin k → M.Carrier .set}
    {G P F sigma : M.Carrier .set} (h : HS A params G P F sigma) : ForcingNames.IsName P sigma := by
  obtain ⟨S,hsigma,hS⟩ := h
  exact ⟨S,hsigma,hS.1⟩

theorem symmetric_of_hs {k : Nat} {A : Formula (k+2)} {params : Fin k → M.Carrier .set}
    {G P F sigma : M.Carrier .set} (h : HS A params G P F sigma) : Symmetric A params G P F sigma := by
  obtain ⟨S,hsigma,hS⟩ := h
  exact hS.2 sigma hsigma

theorem child {k : Nat} {A : Formula (k+2)} {params : Fin k → M.Carrier .set}
    {G P F sigma tau condition : M.Carrier .set} (h : HS A params G P F sigma)
    (he : PureKuratowski.PairMember M tau condition sigma) : HS A params G P F tau := by
  obtain ⟨S,hsigma,hS⟩ := h
  obtain ⟨z,hcode,hz⟩ := he
  obtain ⟨tau',r,hcode',_,htau⟩ := hS.1 sigma hsigma z hz
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact ⟨S,htau,hS⟩

/-- The exact native collection instance; arbitrary surplus witnesses are filtered. -/
theorem collect_witnesses (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F sigma : M.Carrier .set)
    (h : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
      ∃ S, Closed A params G P F S ∧ ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem tau S) :
    ∃ family, (∀ S, (Definitional.Project.FirstOrderSemantics.reduct M).mem S family → Closed A params G P F S) ∧
      ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z sigma →
        ∃ S, (Definitional.Project.FirstOrderSemantics.reduct M).mem S family ∧
          ∃ tau condition, PureKuratowski.Code M z tau condition ∧
            (Definitional.Project.FirstOrderSemantics.reduct M).mem condition P ∧
            (Definitional.Project.FirstOrderSemantics.reduct M).mem tau S := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let inputs : Fin (k+3) → M.Carrier .set := Fin.lastCases F (Fin.lastCases P (Fin.lastCases G params))
  let rho : Fin k → Fin (k+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let gg := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let pp := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let ff := (Fin.last (k+2)).castSucc.castSucc
  let zz := (Fin.last (k+3)).castSucc
  let ss := Fin.last (k+4)
  let matrix := (closed A rho gg pp ff ss).conj (ForcingNames.entry pp zz ss)
  have hm : ∀ z S, Formula.Realize E (Fin.lastCases S (Fin.lastCases z inputs)) matrix ↔
      Closed A params G P F S ∧ ∃ tau condition, PureKuratowski.Code M z tau condition ∧
        E condition P ∧ E tau S := by
    intro z S
    simp only [matrix,E,Formula.Realize,closed_semantics (M := M),ForcingNames.entry_semantics (M := M),
      rho,gg,pp,ff,zz,ss,inputs,Fin.lastCases_last,Fin.lastCases_castSucc]
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) (k+3) :=
    { bound := fun i => inputs i.rev, free := fun _ => sigma }
  have hRel := ForcingMapConditions.binary_semantics hM matrix inputs sigma
  obtain ⟨family,hfamily⟩ := SetTheory.ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary matrix) env sigma (by
      intro z hz
      obtain ⟨S,hS⟩ := h z hz
      exact ⟨S,(hRel z S).mpr ((hm z S).mpr hS)⟩)
  let query := closed A (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc
    (Fin.last (k+2)).castSucc (Fin.last (k+3))
  have hq : ∀ S, Formula.Realize E (Fin.lastCases S inputs) query ↔ Closed A params G P F S := by
    intro S
    simpa only [query,inputs,E,Fin.lastCases_last,Fin.lastCases_castSucc] using
      closed_semantics (M := M) (Fin.lastCases S inputs) A (fun i => i.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc
        (Fin.last (k+2)).castSucc (Fin.last (k+3))
  have sep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨good,hgood⟩ := sep inputs family
  refine ⟨good,fun S hS => (hq S).mp ((hgood S).mp hS).2,?_⟩
  intro z hz
  obtain ⟨S,hS,hw⟩ := hfamily z hz
  obtain ⟨hc,he⟩ := (hm z S).mp ((hRel z S).mp hw)
  exact ⟨S,(hgood S).mpr ⟨hS,(hq S).mpr hc⟩,he⟩

theorem intro_hs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F sigma : M.Carrier .set)
    (hn : ForcingNames.IsName P sigma) (hsym : Symmetric A params G P F sigma)
    (hchild : ∀ tau condition, PureKuratowski.PairMember M tau condition sigma → HS A params G P F tau) :
    HS A params G P F sigma := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨family,hfamily,hentries⟩ := collect_witnesses hM A params G P F sigma (by
    intro z hz
    obtain ⟨tau,condition,hcode,hcondition,_⟩ := ForcingNames.edges hn z hz
    obtain ⟨S,htau,hS⟩ := hchild tau condition ⟨z,hcode,hz⟩
    exact ⟨S,hS,tau,condition,hcode,hcondition,htau⟩)
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_union hKP family
  obtain ⟨S,hS⟩ := SetTheory.KP.exists_insert hKP U sigma
  refine ⟨S,(hS sigma).mpr (Or.inr rfl),?_,?_⟩
  · intro name hname z hz
    rcases (hS name).mp hname with hu | rfl
    · obtain ⟨part,hpart,hnamepart⟩ := (hU name).mp hu
      obtain ⟨tau,condition,hcode,hcondition,htau⟩ := (hfamily part hpart).1 name hnamepart z hz
      exact ⟨tau,condition,hcode,hcondition,(hS tau).mpr (Or.inl ((hU tau).mpr ⟨part,hpart,htau⟩))⟩
    · obtain ⟨part,hpart,tau,condition,hcode,hcondition,htau⟩ := hentries z hz
      exact ⟨tau,condition,hcode,hcondition,(hS tau).mpr (Or.inl ((hU tau).mpr ⟨part,hpart,htau⟩))⟩
  · intro name hname
    rcases (hS name).mp hname with hu | rfl
    · obtain ⟨part,hpart,hnamepart⟩ := (hU name).mp hu
      exact (hfamily part hpart).2 name hnamepart
    · exact hsym

/-- The source equation, with the ambient Name subtype made an object guard. -/
theorem hs_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F sigma : M.Carrier .set) :
    HS A params G P F sigma ↔ ForcingNames.IsName P sigma ∧ Symmetric A params G P F sigma ∧
      ∀ tau condition, PureKuratowski.PairMember M tau condition sigma → HS A params G P F tau := by
  exact ⟨fun h => ⟨isName h,symmetric_of_hs h,fun _ _ he => child h he⟩,
    fun h => intro_hs hM A params G P F sigma h.1 h.2.1 h.2.2⟩

def step {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F sigma : Fin m) : Formula m :=
  (ForcingNames.isName P sigma).conj ((symmetric A rho G P F sigma).conj
    (.all (.all ((Source.SetLanguage.edge sigma.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (hs A (paramsUp (paramsUp rho)) G.castSucc.castSucc P.castSucc.castSucc F.castSucc.castSucc (Fin.last m).castSucc)))))

theorem step_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P F sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (step A rho G P F sigma) ↔
      ForcingNames.IsName (env P) (env sigma) ∧ Symmetric A (fun i => env (rho i)) (env G) (env P) (env F) (env sigma) ∧
      ∀ tau condition, PureKuratowski.PairMember M tau condition (env sigma) →
        HS A (fun i => env (rho i)) (env G) (env P) (env F) tau := by
  simp only [step,Formula.Realize,ForcingNames.isName_semantics (M := M),ForcingStabilizer.symmetric_semantics (M := M),
    KuratowskiZF.source_edge,hs_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def unfoldingSentence {k : Nat} (A : Formula (k+2)) (G P F sigma : Fin k) : Source.Sentence :=
  ((hs A id G P F sigma).iff (step A id G P F sigma)).close

theorem unfolding_models {k : Nat} (A : Formula (k+2)) (G P F sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (unfoldingSentence A G P F sigma)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  have hl := hs_semantics (M := M) env A id G P F sigma
  have hr := step_semantics (M := M) env A id G P F sigma
  have h := hs_iff hM A env (env G) (env P) (env F) (env sigma)
  exact ⟨fun hp => hr.mpr (h.mp (hl.mp hp)),fun hp => hl.mpr (h.mpr (hr.mp hp))⟩

theorem unfolding_kernel_certificate {k : Nat} (A : Formula (k+2)) (G P F sigma : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (unfoldingSentence A G P F sigma)) :=
  ModelTransfer.derives (fun _ hM => unfolding_models A G P F sigma hM)

/-- The actual unary HS formula consumed as H by ForcingFormula, at every rank. -/
def predicate {k : Nat} (A : Formula (k+2)) (G P F : Fin k) : Formula (k+1) :=
  hs A Fin.castSucc G.castSucc P.castSucc F.castSucc (Fin.last k)

theorem predicate_semantics {k : Nat} (A : Formula (k+2)) (G P F : Fin k)
    (params : Fin k → M.Carrier .set) (sigma : M.Carrier .set) :
    ForcingClassEvaluation.Predicate (predicate A G P F) params sigma ↔ HS A params (params G) (params P) (params F) sigma := by
  simpa only [ForcingClassEvaluation.Predicate,predicate,Fin.lastCases_last,Fin.lastCases_castSucc] using
    hs_semantics (M := M) (Fin.lastCases sigma params) A Fin.castSucc G.castSucc P.castSucc F.castSucc (Fin.last k)

/-- Source HS on the empty name; all action witnesses are internal graph codes. -/
theorem empty_hs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F empty : M.Carrier .set)
    (hAction : ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G →
      ∃ r, MapRel A params g r ∧ ForcingConditionGraphs.Endomap P r)
    (htop : (Definitional.Project.FirstOrderSemantics.reduct M).mem G F)
    (hEmpty : ∀ z, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem z empty) :
    HS A params G P F empty := by
  apply intro_hs hM A params G P F empty (ForcingNames.empty_name hM P empty hEmpty)
    (ForcingStabilizer.empty_symmetric hM A params G P F empty hAction htop hEmpty)
  rintro tau condition ⟨z,_,hz⟩
  exact False.elim (hEmpty z hz)

def actionFamily {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) G.castSucc).imp (.ex
    ((ReplacementPredicates.rel A (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).conj
      (ForcingConditionGraphs.endomap P.castSucc.castSucc (Fin.last (m+1))))))

theorem actionFamily_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (G P : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (actionFamily A rho G P) ↔
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g (env G) →
        ∃ r, MapRel A (fun i => env (rho i)) g r ∧ ForcingConditionGraphs.Endomap (env P) r := by
  simp only [actionFamily,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingConditionGraphs.endomap_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def emptySentence {k : Nat} (A : Formula (k+2)) (G P F empty : Fin k) : Source.Sentence :=
  ((actionFamily A id G P).imp ((Formula.mem G F).imp
    ((Formula.all ((Formula.mem (Fin.last k) empty.castSucc).neg)).imp (hs A id G P F empty)))).close

theorem empty_models {k : Nat} (A : Formula (k+2)) (G P F empty : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (emptySentence A G P F empty)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env ha ht he
  exact (hs_semantics (M := M) env A id G P F empty).mpr
    (empty_hs hM A env (env G) (env P) (env F) (env empty)
      ((actionFamily_semantics (M := M) env A id G P).mp ha) ht (by
        simpa only [Definitional.Project.FirstOrderSemantics.reduct,Formula.Realize,Source.Formula.neg,Fin.lastCases_last,Fin.lastCases_castSucc] using he))

theorem empty_kernel_certificate {k : Nat} (A : Formula (k+2)) (G P F empty : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (emptySentence A G P F empty)) :=
  ModelTransfer.derives (fun _ hM => empty_models A G P F empty hM)

/-- The ambient Name guard plus the original Child-recursive equation. -/
def stepWith {k m : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (rho : Fin k → Fin m)
    (G P F sigma : Fin m) : Formula m :=
  (ForcingNames.isName P sigma).conj ((symmetric A rho G P F sigma).conj
    (ForcingNameInduction.below B rho sigma))

theorem stepWith_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (B : Formula (k+1)) (rho : Fin k → Fin m) (G P F sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (stepWith A B rho G P F sigma) ↔
      ForcingNames.IsName (env P) (env sigma) ∧ Symmetric A (fun i => env (rho i)) (env G) (env P) (env F) (env sigma) ∧
      ∀ tau, (∃ condition, PureKuratowski.PairMember M tau condition (env sigma)) →
        Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases tau (fun i => env (rho i))) B := by
  simp only [stepWith,Formula.Realize,ForcingNames.isName_semantics (M := M),ForcingStabilizer.symmetric_semantics (M := M),
    ForcingNameInduction.below,ForcingNameInduction.child_semantics (M := M),ForcingNameInduction.pred_semantics,
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def comparison {k : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (G P F : Fin k) : Formula (k+1) :=
  B.iff (predicate A G P F)

theorem comparison_semantics {k : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (G P F : Fin k)
    (params : Fin k → M.Carrier .set) (sigma : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases sigma params)
      (comparison A B G P F) ↔
    (Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases sigma params) B ↔
      HS A params (params G) (params P) (params F) sigma) := by
  have hh := predicate_semantics (M := M) A G P F params sigma
  change (Formula.Realize _ _ B → ForcingClassEvaluation.Predicate (predicate A G P F) params sigma) ∧
    (ForcingClassEvaluation.Predicate (predicate A G P F) params sigma → Formula.Realize _ _ B) ↔ _
  exact ⟨fun h => ⟨fun hb => hh.mp (h.1 hb),fun hs => h.2 (hh.mpr hs)⟩,
    fun h => ⟨fun hb => hh.mpr (h.mp hb),fun hs => h.mpr (hh.mp hs)⟩⟩

def uniquenessSentence {k : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (G P F : Fin k) : Source.Sentence :=
  ((Formula.all (B.iff (stepWith A B Fin.castSucc G.castSucc P.castSucc F.castSucc (Fin.last k)))).imp
    (.all (comparison A B G P F))).close

/-- Native Child induction identifies the constructed HS with every definable
solution of the literal source equation, including nonstandard models. -/
theorem uniqueness_models {k : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (G P F : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence A B G P F)).TrueIn M := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics E _).mpr
  intro env heq
  have eqAt : ∀ sigma, Formula.Realize E (Fin.lastCases sigma env) B ↔
      ForcingNames.IsName (env P) sigma ∧ Symmetric A env (env G) (env P) (env F) sigma ∧
      ∀ tau, (∃ condition, PureKuratowski.PairMember M tau condition sigma) → Formula.Realize E (Fin.lastCases tau env) B := by
    intro sigma
    have h := heq sigma
    have ht := stepWith_semantics (M := M) (Fin.lastCases sigma env) A B Fin.castSucc
      G.castSucc P.castSucc F.castSucc (Fin.last k)
    simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at ht
    exact ⟨fun hb => ht.mp (h.1 hb),fun hc => h.2 (ht.mpr hc)⟩
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate (comparison A B G P F)).semantically_entails M hM)) env
  change Formula.Realize E env (ForcingNameInduction.progressive (comparison A B G P F) id) →
    Formula.Realize E env (SetInductionSyntax.holds (comparison A B G P F) id) at hi
  have hall := hi ((ForcingNameInduction.progressive_semantics env (comparison A B G P F) id).mpr (by
    intro sigma ih
    apply (comparison_semantics A B G P F env sigma).mpr
    constructor
    · intro hb
      obtain ⟨hn,hsym,hchild⟩ := (eqAt sigma).mp hb
      apply intro_hs hM A env (env G) (env P) (env F) sigma hn hsym
      intro tau condition he
      exact ((comparison_semantics A B G P F env tau).mp (ih tau ⟨condition,he⟩)).mp (hchild tau ⟨condition,he⟩)
    · intro hsigma
      apply (eqAt sigma).mpr
      refine ⟨isName hsigma,symmetric_of_hs hsigma,?_⟩
      rintro tau ⟨condition,he⟩
      exact ((comparison_semantics A B G P F env tau).mp (ih tau ⟨condition,he⟩)).mpr (child hsigma he)))
  exact (ForcingNameInduction.holds_semantics E env (comparison A B G P F) id).mp hall

theorem uniqueness_kernel_certificate {k : Nat} (A : Formula (k+2)) (B : Formula (k+1)) (G P F : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence A B G P F)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models A B G P F hM)

end PPAC.Migration.ForcingHS
