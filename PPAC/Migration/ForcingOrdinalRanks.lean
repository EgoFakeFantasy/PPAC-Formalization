/- Pinned OrdinalCodes.selectedRankFixed/selectedRankFixed_eq and selectionType.
The recursion is on INTERNAL ordinals, then reindexed along the existing
internal wellorder collapse. No host WellFounded assumption is used. -/
import PPAC.Migration.ForcingCollectedName
import PPAC.Migration.ConstructionTowerIteration
import YesMetaZFC.SetTheory.Ord.OrderType

namespace PPAC.Migration.ForcingOrdinalRanks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn)
open ForcingMapConditions (MapRel)
open ForcingCollectedName (Collected)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source collect step, using the exact domain of its internal history. -/
def Step {n : Nat} (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P history output : M.Carrier .set) : Prop :=
  ∃ J, FunctionOn J history ∧ Collected R env J history P output

def step {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (P history output : Fin m) : Project.Formula 1 m :=
  .existsE (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.functionOn history.succ 0))
    (ProjectSyntax.encode id (ForcingCollectedName.collected R (fun i => (rho i).succ)
      0 history.succ P.succ output.succ)))

theorem step_freeClosed {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (P history output : Fin m) : (step R rho P history output).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P history output : Fin m) :
    Project.Formula.satisfies env (step R rho P history output) ↔
      Step R (fun i => env.bound (rho i)) (env.bound P) (env.bound history) (env.bound output) := by
  simp only [step,Step,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingCollectedName.collected_semantics (M := M)]
  rfl

def operator {n : Nat} (R : Source.Formula (n+2)) : Project.BinarySchema (n+1) where
  body := step R (fun i => i.succ.succ.succ) 2 1 0
  freeClosed := step_freeClosed ..

def operatorEnv {n : Nat} (env : Fin n → M.Carrier .set) (P : M.Carrier .set) :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) (n+1) where
  bound := Fin.cases P env
  free := fun _ => P

theorem operator_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set) (P history output : M.Carrier .set) :
    (operator R).denote (operatorEnv env P) history output ↔ Step R env P history output :=
  step_semantics hM R (fun i => i.succ.succ.succ)
    (((operatorEnv env P).push history).push output) 2 1 0

theorem sequence_function (hM : FirstOrder.Theory.Models M nativeZF)
    {history J : M.Carrier .set}
    (h : (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength
      (KuratowskiZF.interpretation hM) history J) : FunctionOn J history := by
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨x,y,hc⟩ := h.2.1.1 z hz
    exact ⟨x,y,(h.2.2 x).mpr ⟨y,z,hc,hz⟩,hc⟩
  · intro x hx
    obtain ⟨y,hy⟩ := (h.2.2 x).mp hx
    exact ⟨y,hy,fun z hz => h.2.1.2 x z y hz hy⟩

theorem class_function (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set) (P : M.Carrier .set) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnTransfiniteSequences
      (KuratowskiZF.interpretation hM) ((operator R).denote (operatorEnv env P)) := by
  rintro history ⟨J,hJ⟩
  obtain ⟨out,hOut⟩ := ForcingCollectedName.exists_collected hM R env J history P
  refine ⟨out,(operator_semantics hM R env P history out).mpr
    ⟨J,sequence_function hM hJ,hOut⟩,?_⟩
  intro other hOther
  obtain ⟨K,hK,hOther⟩ := (operator_semantics hM R env P history other).mp hOther
  have hKJ := ConstructionTowerIteration.length_unique hM hK (sequence_function hM hJ)
  subst K
  exact ForcingCollectedName.unique hM hOther hOut

/-- One set graph on the WHOLE internal ordinal, with the literal collect equation. -/
def OrdinalRanks {n : Nat} (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P length history : M.Carrier .set) : Prop :=
  FunctionOn length history ∧ ∀ index value,
    (Project.FirstOrderSemantics.reduct M).mem index length →
    PureKuratowski.PairMember M index value history → Collected R env index history P value

theorem ordinal_ranks_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set) (P : M.Carrier .set)
    {length : M.Carrier .set} (hLength : (Project.FirstOrderSemantics.reduct M).IsOrdinal length) :
    ∃ history, OrdinalRanks R env P length history := by
  obtain ⟨history,hSequence,hRecursion⟩ := ZF.recursiveSequence_exists
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (operatorEnv env P) (operator R) (class_function hM R env P) hLength
  refine ⟨history,sequence_function hM hSequence,?_⟩
  intro index value hi hv
  obtain ⟨restriction,hr,hop⟩ := hRecursion index hi value hv
  obtain ⟨J,hJ,hOut⟩ := (operator_semantics hM R env P restriction value).mp hop
  have hJI := ConstructionTowerIteration.length_unique hM hJ
    (sequence_function hM (hSequence.restriction hi hr))
  subst J
  intro z
  rw [hOut z]
  constructor
  · rintro ⟨child,p,⟨hp,i,hi,hic,hR⟩,hc⟩
    exact ⟨child,p,⟨hp,i,hi,((hr.2 i child).mp hic).2,hR⟩,hc⟩
  · rintro ⟨child,p,⟨hp,i,hi,hic,hR⟩,hc⟩
    exact ⟨child,p,⟨hp,i,hi,(hr.2 i child).mpr ⟨hi,hic⟩,hR⟩,hc⟩

def transported {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X collapse i p : Fin m) : Source.Formula m :=
  .ex ((Source.Formula.mem (Fin.last m) X.castSucc).conj
    ((Source.SetLanguage.edge collapse.castSucc (Fin.last m) i.castSucc).conj
      (ReplacementPredicates.rel R (ReplacementPredicates.paramsUp rho) (Fin.last m) p.castSucc)))

def Transported {n : Nat} (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    (X collapse i p : M.Carrier .set) : Prop :=
  ∃ a, (Project.FirstOrderSemantics.reduct M).mem a X ∧
    PureKuratowski.PairMember M a i collapse ∧ MapRel R env a p

theorem transported_semantics {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (X collapse i p : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (transported R rho X collapse i p) ↔
    Transported R (fun j => env (rho j)) (env X) (env collapse) (env i) (env p) := by
  simp only [transported,Transported,Source.Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),ReplacementPredicates.paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]

def pullback {n : Nat} (R : Source.Formula (n+2)) : Source.Formula ((n+2)+2) :=
  transported R (fun j => j.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3))

theorem pullback_semantics {n : Nat} (R : Source.Formula (n+2))
    (env : Fin n → M.Carrier .set) (X collapse i p : M.Carrier .set) :
    MapRel (pullback R) (Fin.lastCases collapse (Fin.lastCases X env)) i p ↔
      Transported R env X collapse i p := by
  simp only [MapRel,pullback,transported_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Literal predecessor edge predicate from selectedRankFixed_eq. -/
def PredEntry {n : Nat} (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    (X order ranks P a z : M.Carrier .set) : Prop :=
  ∃ child p, ((Project.FirstOrderSemantics.reduct M).mem p P ∧ ∃ b,
    (Project.FirstOrderSemantics.reduct M).mem b X ∧
    PureKuratowski.PairMember M b a order ∧ PureKuratowski.PairMember M b child ranks ∧
    MapRel R env b p) ∧ PureKuratowski.Code M z child p

def Ranks {n : Nat} (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    (X order P ranks : M.Carrier .set) : Prop :=
  FunctionOn X ranks ∧ ∀ a value,
    (Project.FirstOrderSemantics.reduct M).mem a X →
    PureKuratowski.PairMember M a value ranks →
    ∀ z, (Project.FirstOrderSemantics.reduct M).mem z value ↔ PredEntry R env X order ranks P a z

/-- The arbitrary INTERNAL wellorder of the source, with its original indices.
The existing collapse, native recursion and composition constructors are reused. -/
theorem ranks_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    {X order : M.Carrier .set} (P : M.Carrier .set)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X) :
    ∃ ranks, Ranks R env X order P ranks := by
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨alpha,hType,_⟩ := ZF.wellOrderType_existsUnique hZF I hOrder
  have hAlpha := hType.isOrdinal hZF I hOrder
  obtain ⟨collapse,hCollapse,hRange⟩ := hType
  let pe : Fin (n+2) → M.Carrier .set := Fin.lastCases collapse (Fin.lastCases X env)
  obtain ⟨history,hHistory,hRow⟩ := ordinal_ranks_exists hM (pullback R) pe P hAlpha
  obtain ⟨bound,hBound⟩ := ForcingMapConditions.coordinate_bound hM history
  have hInto : ForcingSupportSize.MapsTo alpha bound history :=
    ⟨hHistory,fun x y he => (hBound x y he).2⟩
  have hCollapseMap : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I collapse X alpha := by
    refine ⟨hCollapse.1,hCollapse.2.1,?_⟩
    intro a ha
    obtain ⟨i,hi⟩ := (hCollapse.2.1 a).mp ha
    exact ⟨i,(hRange i).mpr ⟨a,hi⟩,hi⟩
  obtain ⟨ranks,hRanks,hGraph⟩ := ZF.exists_compositionFunction hZF I hCollapseMap
    ((ForcingSupportSize.native_mapsTo hM alpha bound history).mp hInto)
  refine ⟨ranks,((ForcingSupportSize.native_mapsTo hM X bound ranks).mpr hRanks).1,?_⟩
  intro a value ha hav z
  obtain ⟨_,i,hai,hiv⟩ := (hGraph a value).mp hav
  have hi : (Project.FirstOrderSemantics.reduct M).mem i alpha := (hRange i).mpr ⟨a,hai⟩
  rw [hRow i value hi hiv z]
  constructor
  · rintro ⟨child,p,⟨hp,j,hji,hjc,hSel⟩,hc⟩
    obtain ⟨b,hb,hbj,hR⟩ := (pullback_semantics R env X collapse j p).mp hSel
    have hba := (hCollapse.relation_iff_mem hZF I hOrder hbj hai).mpr hji
    exact ⟨child,p,⟨hp,b,hb,hba,(hGraph b child).mpr ⟨hb,j,hbj,hjc⟩,hR⟩,hc⟩
  · rintro ⟨child,p,⟨hp,b,hb,hba,hbc,hR⟩,hc⟩
    obtain ⟨_,j,hbj,hjc⟩ := (hGraph b child).mp hbc
    have hji := (hCollapse.relation_iff_mem hZF I hOrder hbj hai).mp hba
    exact ⟨child,p,⟨hp,j,hji,hjc,(pullback_semantics R env X collapse j p).mpr ⟨b,hb,hbj,hR⟩⟩,hc⟩

def NameAt (P history a : M.Carrier .set) : Prop :=
  ∀ value, PureKuratowski.PairMember M a value history → ForcingNames.IsName P value

def nameAt {m : Nat} (P history a : Fin m) : Source.Formula m :=
  .all ((Source.SetLanguage.edge history.castSucc a.castSucc (Fin.last m)).imp
    (ForcingNames.isName P.castSucc (Fin.last m)))

theorem nameAt_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P history a : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (nameAt P history a) ↔
      NameAt (env P) (env history) (env a) := by
  simp only [nameAt,NameAt,Source.Formula.Realize,KuratowskiZF.source_edge,
    ForcingNames.isName_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Names (P X history : M.Carrier .set) : Prop :=
  ∀ a, (Project.FirstOrderSemantics.reduct M).mem a X → NameAt P history a

def names {m : Nat} (P X history : Fin m) : Source.Formula m :=
  .all ((Source.Formula.mem (Fin.last m) X.castSucc).imp (nameAt P.castSucc history.castSucc (Fin.last m)))

theorem names_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P X history : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (names P X history) ↔
      Names (env P) (env X) (env history) := by
  simp only [names,Names,Source.Formula.Realize,nameAt_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Internal wellorder induction, justified by a separated counterexample SET. -/
theorem ranks_names (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Source.Formula (n+2)} {env : Fin n → M.Carrier .set}
    {X order P history : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X) (hRanks : Ranks R env X order P history) :
    Names P X history := by
  let inputs : Fin 2 → M.Carrier .set := Fin.cases P (fun _ => history)
  let query : Source.Formula 3 := (nameAt 0 1 2).imp .bot
  have hq : ∀ a, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases a inputs) query ↔ ¬ NameAt P history a := by
    intro a
    simp only [query,Source.Formula.Realize,nameAt_semantics (M := M)]
    rfl
  have hsep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨bad,hBad⟩ := hsep inputs X
  apply hOrder.induction (ModelTransfer.extensionality hM) (NameAt P history)
    ⟨bad,fun a => (hBad a).trans (and_congr Iff.rfl (hq a))⟩
  intro a ha ih value hv
  apply ForcingNames.intro_name hM P value
  intro z hz
  obtain ⟨child,p,⟨hp,b,hb,hba,hbc,_⟩,hc⟩ := (hRanks.2 a value ha hv z).mp hz
  exact ⟨child,p,hc,hp,ih b hb hba child hbc⟩

/-- Source selectionType uses this SAME rank graph. -/
theorem ranks_and_type_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Source.Formula (n+2)) (env : Fin n → M.Carrier .set)
    {X order : M.Carrier .set} (P : M.Carrier .set)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X) :
    ∃ ranks selection, Ranks R env X order P ranks ∧ Collected R env X ranks P selection ∧
      Names P X ranks ∧ ForcingNames.IsName P selection := by
  obtain ⟨ranks,hr⟩ := ranks_exists hM R env P hOrder
  obtain ⟨selection,hs⟩ := ForcingCollectedName.exists_collected hM R env X ranks P
  have hn := ranks_names hM hOrder hr
  exact ⟨ranks,selection,hr,hs,hn,ForcingCollectedName.isName hM hs (fun a value ha hv => hn a ha value hv)⟩

def predAdmissible {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order ranks P a child p : Fin m) : Source.Formula m :=
  (Source.Formula.mem p P).conj (.ex ((Source.Formula.mem (Fin.last m) X.castSucc).conj
    ((Source.SetLanguage.edge order.castSucc (Fin.last m) a.castSucc).conj
      ((Source.SetLanguage.edge ranks.castSucc (Fin.last m) child.castSucc).conj
        (ReplacementPredicates.rel R (ReplacementPredicates.paramsUp rho) (Fin.last m) p.castSucc)))))

def predEntry {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order ranks P a z : Fin m) : Source.Formula m :=
  .ex (.ex ((predAdmissible R (ReplacementPredicates.paramsUp (ReplacementPredicates.paramsUp rho))
    X.castSucc.castSucc order.castSucc.castSucc ranks.castSucc.castSucc P.castSucc.castSucc
    a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem predEntry_semantics {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (X order ranks P a z : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (predEntry R rho X order ranks P a z) ↔
    PredEntry R (fun i => env (rho i)) (env X) (env order) (env ranks) (env P) (env a) (env z) := by
  simp only [predEntry,predAdmissible,PredEntry,Source.Formula.Realize,
    KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingMapConditions.rel_semantics (M := M),ReplacementPredicates.paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def ranks {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order P history : Fin m) : Source.Formula m :=
  (Source.SetLanguage.functionOn history X).conj
    (.all ((Source.Formula.mem (Fin.last m) X.castSucc).imp (.all
      ((Source.SetLanguage.edge history.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
        (.all ((Source.Formula.mem (Fin.last (m+2)) (Fin.last (m+1)).castSucc).iff
          (predEntry R (ReplacementPredicates.paramsUp (ReplacementPredicates.paramsUp
            (ReplacementPredicates.paramsUp rho))) X.castSucc.castSucc.castSucc
              order.castSucc.castSucc.castSucc history.castSucc.castSucc.castSucc
              P.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)))))))))

theorem ranks_semantics {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (X order P history : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (ranks R rho X order P history) ↔
    Ranks R (fun i => env (rho i)) (env X) (env order) (env P) (env history) := by
  simp only [ranks,Ranks,Source.Formula.Realize,Source.Formula.iff,
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,
    predEntry_semantics (M := M),ReplacementPredicates.paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h => ⟨h.1,fun a value ha hv z => ⟨(h.2 a ha value hv z).1,(h.2 a ha value hv z).2⟩⟩,
    fun h => ⟨h.1,fun a ha value hv z => ⟨(h.2 a value ha hv z).mp,(h.2 a value ha hv z).mpr⟩⟩⟩

/-- Pure-membership existence of the actual rank graph and its selection type.
Names are proved by internal induction. HS/fixation and forcing are subsequent consumers. -/
def constructionSentence {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order P : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (.existsE (.existsE (.conj
      (ProjectSyntax.encode id (ranks R (fun i => (rho i).succ.succ)
        X.succ.succ order.succ.succ P.succ.succ 1))
      (.conj (ProjectSyntax.encode id (ForcingCollectedName.collected R (fun i => (rho i).succ.succ)
        X.succ.succ 1 P.succ.succ 0)) (.conj
        (ProjectSyntax.encode id (names P.succ.succ X.succ.succ 1))
        (ProjectSyntax.encode id (ForcingNames.isName P.succ.succ 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem construction_models {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order P : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence R rho X order P)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    names_semantics (M := M),ForcingNames.isName_semantics (M := M)]
  exact fun hOrder => ranks_and_type_exists hM R (fun i => bound (rho i)) (bound P) hOrder

theorem construction_kernel_certificate {n m : Nat} (R : Source.Formula (n+2)) (rho : Fin n → Fin m)
    (X order P : Fin m) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence R rho X order P)) :=
  ModelTransfer.derives (fun _ hM => construction_models R rho X order P hM)

end PPAC.Migration.ForcingOrdinalRanks
