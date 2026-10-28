/- Pinned AvailableRecords.eligibleSystem.Obj:272 and LocalRecords.System.Obj:532.
Assemble one internal family over ALL internal diagrams using the unchanged
native functional-image and function-graph constructors. Row witnesses are the
actual range, fixing subgroup, LocalName set, quotient and projection.
Uniqueness eliminates any need for a host choice of such witnesses. -/
import PPAC.Migration.ForcingEligibleLaws

namespace PPAC.Migration.ForcingEligibleFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (MapsTo Injection)
open ForcingSupportedNames (Range)
open ForcingLocalQuotient (Classes Projection)
open ForcingProductSymmetry (orderFormula)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Data {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g q nameBound labels E r A fixing X Q pr O : M.Carrier .set) : Prop :=
  Range (v 0) r A ∧ ForcingLabelPermutations.Fixing G A fixing ∧
    ForcingLocalNames.Carrier v G F nameBound fixing X ∧ MapsTo X Q pr ∧
    Classes R env (v 6) g r X Q ∧ Projection R env (v 6) g r X pr ∧
    ForcingEligibleObjects.Carrier R Hdom env (v 0) mul (v 6) g r q labels E pr Q O

def data {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E r A fixing X Q pr O : Fin m) : Formula m :=
  (ForcingSupportedNames.range (rho 0) r A).conj
    ((ForcingLabelPermutations.fixing G A fixing).conj
      ((ForcingLocalNames.carrier rho G F nameBound fixing X).conj
        ((Source.SetLanguage.mapsTo pr X Q).conj
          ((ForcingLocalQuotient.classes R base (rho 6) g r X Q).conj
            ((ForcingLocalQuotient.projection R base (rho 6) g r X pr).conj
              (ForcingEligibleObjects.carrier R Hdom base (rho 0) mul (rho 6) g r q labels E pr Q O))))))

theorem data_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E r A fixing X Q pr O : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (data R Hdom base rho G F mul g q nameBound labels E r A fixing X Q pr O) ↔
    Data R Hdom (fun j => env (base j)) (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) (env r)
      (env A) (env fixing) (env X) (env Q) (env pr) (env O) := by
  simp only [data,Data,Formula.Realize,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingLocalNames.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLocalQuotient.classes_semantics (M := M),
    ForcingLocalQuotient.projection_semantics (M := M),ForcingEligibleObjects.carrier_semantics (M := M)]

def Row {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g q nameBound labels E r O : M.Carrier .set) : Prop :=
  ∃ A fixing X Q pr, Data R Hdom env v G F mul g q nameBound labels E r A fixing X Q pr O

def row {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E r O : Fin m) : Formula m :=
  let up : Fin m → Fin (m+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let A := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let fixing := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let X := (Fin.last (m+2)).castSucc.castSucc
  let Q := (Fin.last (m+3)).castSucc
  let pr := Fin.last (m+4)
  .ex (.ex (.ex (.ex (.ex (data R Hdom (fun j => up (base j)) (fun j => up (rho j))
    (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) (up r) A fixing X Q pr (up O))))))

theorem row_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E r O : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (row R Hdom base rho G F mul g q nameBound labels E r O) ↔
    Row R Hdom (fun j => env (base j)) (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) (env r) (env O) := by
  simp only [row,Row,Formula.Realize,data_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_row (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F mul g q nameBound labels E : M.Carrier .set)
    {I r : M.Carrier .set} (hr : Injection (v 0) I r) :
    ∃ O, Row R Hdom env v G F mul g q nameBound labels E r O := by
  have hn := (ForcingSupportSize.native_injection hM (v 0) I r).mp hr
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hn.1.1 hn.1.2.1
  have hRange : Range (v 0) r A := fun z => ⟨fun hz => by
    obtain ⟨x,hxz⟩ := (hA z).mp hz
    exact ⟨x,ForcingConditionGraphs.function_input hr.1.1 hxz,hxz⟩,
    fun ⟨x,_,hxz⟩ => (hA z).mpr ⟨x,hxz⟩⟩
  obtain ⟨fixing,hFix⟩ := ForcingLabelPermutations.exists_fixing hM G A
  obtain ⟨X,hX⟩ := ForcingLocalNames.exists_carrier hM v G F nameBound fixing
  obtain ⟨Q,pr,hpr,hQ,hPr⟩ := ForcingLocalQuotient.exists_quotient hM R env (v 6) g r X
  -- Same existing Obj Separation, with the internally quantified row values
  -- added as parameters; no new bound, selection or graph backend.
  let values : Fin 9 → M.Carrier .set := Fin.cases (v 0) (Fin.cases mul (Fin.cases (v 6)
    (Fin.cases g (Fin.cases r (Fin.cases q (Fin.cases labels (args2 E pr)))))))
  let params : Fin (k+9) → M.Carrier .set := Fin.addCases env values
  let up : Fin k → Fin (k+9) := Fin.castAdd 9
  let slot : Fin 9 → Fin (k+9) := Fin.natAdd k
  let test : Formula (k+9+1) :=
    (ForcingDiagramOrder.le (slot 0).castSucc (slot 1).castSucc (slot 4).castSucc (slot 5).castSucc).conj
      (ForcingEligibility.eligible R Hdom (paramsUp up) (slot 2).castSucc (slot 3).castSucc
        (slot 4).castSucc (slot 6).castSucc (slot 7).castSucc (slot 8).castSucc (Fin.last (k+9)))
  have ht : ∀ x, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x params) test ↔ ForcingDiagramOrder.Le (v 0) mul r q ∧
        ForcingEligibility.Eligible R Hdom env (v 6) g r labels E pr x := by
    intro x
    simp only [test,Formula.Realize,ForcingDiagramOrder.le_semantics (M := M),
      ForcingEligibility.eligible_semantics (M := M),paramsUp,params,up,slot,values,
      Fin.lastCases_last,Fin.lastCases_castSucc,Fin.addCases_left,Fin.addCases_right,
      Fin.cases_zero]
    rfl
  have sep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem test).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation test).semantically_entails M hM))
  obtain ⟨O,hO⟩ := sep params Q
  exact ⟨O,A,fixing,X,Q,pr,hRange,hFix,hX,hpr,hQ,hPr,
    fun x => (hO x).trans (and_congr Iff.rfl (ht x))⟩

theorem data_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E r A H X Q pr O A' H' X' Q' pr' P : M.Carrier .set}
    (hO : Data R Hdom env v G F mul g q nameBound labels E r A H X Q pr O)
    (hP : Data R Hdom env v G F mul g q nameBound labels E r A' H' X' Q' pr' P) :
    A = A' ∧ H = H' ∧ X = X' ∧ Q = Q' ∧ pr = pr' ∧ O = P := by
  obtain ⟨hA,hH,hX,hpr,hQ,hPr,hO⟩ := hO
  obtain ⟨hA',hH',hX',hpr',hQ',hPr',hP⟩ := hP
  have hAA := (ModelTransfer.extensionality hM).eq_of_same_members A A'
    (fun z => (hA z).trans (hA' z).symm)
  subst A'
  have hHH := ForcingLabelPermutations.fixing_unique hM hH hH'
  subst H'
  have hXX := ForcingLocalNames.unique hM hX hX'
  subst X'
  have hQQ := (ModelTransfer.extensionality hM).eq_of_same_members Q Q'
    (fun z => (hQ z).trans (hQ' z).symm)
  subst Q'
  have hPP : pr = pr' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM X Q pr).mp hpr).1.1
    ((ForcingSupportSize.native_mapsTo hM X Q pr').mp hpr').1.1
    (fun x y => (hPr x y).trans (hPr' x y).symm)
  subst pr'
  exact ⟨rfl,rfl,rfl,rfl,rfl,(ModelTransfer.extensionality hM).eq_of_same_members O P
    (fun x => (hO x).trans (hP x).symm)⟩

theorem row_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E r O P : M.Carrier .set}
    (hO : Row R Hdom env v G F mul g q nameBound labels E r O)
    (hP : Row R Hdom env v G F mul g q nameBound labels E r P) : O = P := by
  obtain ⟨A,H,X,Q,pr,hO⟩ := hO
  obtain ⟨A',H',X',Q',pr',hP⟩ := hP
  exact (data_unique hM hO hP).2.2.2.2.2

def Family {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g q nameBound labels E diagrams objects : M.Carrier .set) : Prop :=
  ∀ r O, PureKuratowski.PairMember M r O objects ↔
    (Project.FirstOrderSemantics.reduct M).mem r diagrams ∧
      Row R Hdom env v G F mul g q nameBound labels E r O

def family {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E diagrams objects : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge objects.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc diagrams.castSucc.castSucc).conj
      (row R Hdom (paramsUp (paramsUp base)) (paramsUp (paramsUp rho)) G.castSucc.castSucc
        F.castSucc.castSucc mul.castSucc.castSucc g.castSucc.castSucc q.castSucc.castSucc
        nameBound.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1))))))

theorem family_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E diagrams objects : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (family R Hdom base rho G F mul g q nameBound labels E diagrams objects) ↔
    Family R Hdom (fun j => env (base j)) (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) (env diagrams) (env objects) := by
  simp only [family,Family,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    row_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h r O => ⟨(h r O).1,(h r O).2⟩,fun h r O => ⟨(h r O).mp,(h r O).mpr⟩⟩

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul g q nameBound labels E I diagrams : Fin k)
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams)) :
    ∃ image objects, MapsTo (env diagrams) image objects ∧
      Family R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) (env g) (env q)
        (env nameBound) (env labels) (env E) (env diagrams) objects := by
  let up : Fin k → Fin (k+2) := fun i => i.castSucc.castSucc
  let query := row R Hdom up (fun j => up (rho j)) (up G) (up F) (up mul) (up g)
    (up q) (up nameBound) (up labels) (up E) (Fin.last k).castSucc (Fin.last (k+1))
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k :=
    { bound := fun i => env i.rev, free := fun _ => env diagrams }
  have hRel : ∀ r O, (ProjectSyntax.binary query).denote penv r O ↔
      Row R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) (env g) (env q)
        (env nameBound) (env labels) (env E) r O := by
    intro r O
    rw [ForcingMapConditions.binary_semantics hM query env (env diagrams) r O]
    simp only [ForcingMapConditions.MapRel,query,row_semantics (M := M),up,
      Fin.lastCases_last,Fin.lastCases_castSucc]
  have ht : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env diagrams) →
      ∃ O, (ProjectSyntax.binary query).denote penv r O := by
    intro r hr
    obtain ⟨O,hO⟩ := exists_row hM R Hdom env (fun j => env (rho j)) (env G) (env F)
      (env mul) (env g) (env q) (env nameBound) (env labels) (env E) ((hDiagrams r).mp hr)
    exact ⟨O,(hRel r O).mpr hO⟩
  have hu : ∀ r O P, (ProjectSyntax.binary query).denote penv r O →
      (ProjectSyntax.binary query).denote penv r P → O = P := by
    intro r O P hO hP
    exact row_unique hM ((hRel r O).mp hO) ((hRel r P).mp hP)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) penv (env diagrams) ht hu
  obtain ⟨objects,hObj,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv
    ht (fun r _ O P hO hP => hu r O P hO hP)
    (fun r O hr hO => (hImage O).mpr ⟨r,hr,hO⟩)
  exact ⟨image,objects,(ForcingSupportSize.native_mapsTo hM (env diagrams) image objects).mpr hObj,
    fun r O => (hEdge r O).trans (and_congr Iff.rfl (hRel r O))⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul g q nameBound labels E I diagrams : Fin k) : Source.Sentence :=
  let up : Fin k → Fin (k+2) := fun i => i.castSucc.castSucc
  ((ForcingDiagramCarrier.carrier (rho 0) I diagrams).imp
    (.ex (.ex ((Source.SetLanguage.mapsTo (Fin.last (k+1)) (up diagrams) (Fin.last k).castSucc).conj
      (family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up
        (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up q) (up nameBound)
        (up labels) (up E) (up diagrams) (Fin.last (k+1))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul g q nameBound labels E I diagrams : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho G F mul g q nameBound labels E I diagrams)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hDiagrams
  obtain ⟨image,objects,hMap,hFamily⟩ := exists_family hM (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env rho G F mul g q nameBound labels E I diagrams
    ((ForcingDiagramCarrier.carrier_semantics (M := M) env (rho 0) I diagrams).mp hDiagrams)
  refine ⟨image,objects,?_,?_⟩
  · apply (ForcingSupportSize.mapsTo_semantics (M := M) (Fin.lastCases objects (Fin.lastCases image env))
      (Fin.last (k+1)) diagrams.castSucc.castSucc (Fin.last k).castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hMap
  · apply (family_semantics (M := M) (Fin.lastCases objects (Fin.lastCases image env))
      (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      (fun i => i.castSucc.castSucc) (fun j => (rho j).castSucc.castSucc)
      G.castSucc.castSucc F.castSucc.castSucc mul.castSucc.castSucc g.castSucc.castSucc
      q.castSucc.castSucc nameBound.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc
      diagrams.castSucc.castSucc (Fin.last (k+1))).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hFamily

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul g q nameBound labels E I diagrams : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho G F mul g q nameBound labels E I diagrams)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho G F mul g q nameBound labels E I diagrams hM)

end PPAC.Migration.ForcingEligibleFamily
