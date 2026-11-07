/- Pinned Models/OrdinalChoice.maximal_antichain:16-49, at the Cohen
instance used by localized_maximum. Reuse the existing internal ordinal
enumeration and native transfinite recursion. No host well-foundedness,
Zorn axiom, supplied maximal set or new recursion/choice backend. -/
import PPAC.Migration.ForcingLocalizedExistential
import PPAC.Migration.ExistingOrdinalEnumeration

namespace PPAC.Migration.ForcingMaximalAntichain
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCohenCompatibility (Compatible)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Prior (history x : M.Carrier .set) : Prop :=
  ∃ i A, PureKuratowski.PairMember M i A history ∧ (Project.FirstOrderSemantics.reduct M).mem x A

def prior {n : Nat} (history x : Fin n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge history.succ.succ 1 0))
    (.mem (.bound x.succ.succ) (.bound 0))))

theorem prior_freeClosed {n : Nat} (history x : Fin n) : (prior history x).FreeClosed := by
  simp -implicitDefEqProofs [prior,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem prior_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (history x : Fin n) :
    Project.Formula.satisfies env (prior history x) ↔ Prior (env.bound history) (env.bound x) := by
  simp only [prior,Prior,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  rfl

def Selected (hM : FirstOrder.Theory.Models M nativeZF) (enumeration history x : M.Carrier .set) : Prop :=
  ∃ i, (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength (KuratowskiZF.interpretation hM) history i ∧
    PureKuratowski.PairMember M i x enumeration ∧ ∀ y, Prior history y → ¬ Compatible x y

def selected {n : Nat} (enumeration history x : Fin n) : Project.Formula 1 n :=
  .existsE (.conj (Project.Formula.isSequenceOfLength PureKuratowskiProject.convention (.bound history.succ) (.bound 0))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge enumeration.succ 0 x.succ))
      (.forallE (.imp (prior history.succ.succ 0)
        (.neg (ConstructionCompatiblePlacement.compatible x.succ.succ 0))))))

theorem selected_freeClosed {n : Nat} (enumeration history x : Fin n) :
    (selected enumeration history x).FreeClosed := by
  simp -implicitDefEqProofs [selected,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isSequenceOfLength_freeClosed,prior_freeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (enumeration history x : Fin n) :
    Project.Formula.satisfies env (selected enumeration history x) ↔
      Selected hM (env.bound enumeration) (env.bound history) (env.bound x) := by
  simp only [selected,Selected,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_isSequenceOfLength_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    prior_semantics hM,ConstructionCompatiblePlacement.compatible_semantics hM]
  rfl

def Operation (hM : FirstOrder.Theory.Models M nativeZF) (D enumeration history A : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x A ↔
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ (Prior history x ∨ Selected hM enumeration history x)

def operation {n : Nat} (D enumeration history A : Fin n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) (.bound A.succ))
    (.conj (.mem (.bound 0) (.bound D.succ)) (.disj (prior history.succ 0) (selected enumeration.succ history.succ 0))))

theorem operation_freeClosed {n : Nat} (D enumeration history A : Fin n) :
    (operation D enumeration history A).FreeClosed := by
  simp -implicitDefEqProofs [operation,Definitional.Formula.FreeClosed,prior_freeClosed,selected_freeClosed]

theorem operation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (D enumeration history A : Fin n) :
    Project.Formula.satisfies env (operation D enumeration history A) ↔
      Operation hM (env.bound D) (env.bound enumeration) (env.bound history) (env.bound A) := by
  simp only [operation,Operation,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,prior_semantics hM,selected_semantics hM]
  rfl

theorem operation_exists_unique (hM : FirstOrder.Theory.Models M nativeZF) (D enumeration history : M.Carrier .set) :
    ∃ A, Operation hM D enumeration history A ∧ ∀ B, Operation hM D enumeration history B → B = A := by
  let env : Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Fin.cases enumeration (fun _ => history),fun _ => D⟩
  let schema : Project.UnarySchema 2 := {
    body := .disj (prior 2 0) (selected 1 2 0)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,prior_freeClosed,selected_freeClosed] }
  have he x : schema.denote env x ↔ Prior history x ∨ Selected hM enumeration history x := by
    simp only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_disj_iff,prior_semantics hM,selected_semantics hM]
    rfl
  obtain ⟨A,hA⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env D
  have hOp : Operation hM D enumeration history A := fun x => (hA x).trans (and_congr_right fun _ => he x)
  exact ⟨A,hOp,fun B hB => (ModelTransfer.extensionality hM).eq_of_same_members B A
    (fun x => (hB x).trans (hOp x).symm)⟩

/-- Instantiate the existing native recursion with the explicit separation
operator; all sequence lengths may be externally nonstandard/ill-founded. -/
theorem recursive_exists (hM : FirstOrder.Theory.Models M nativeZF) {D enumeration kappa : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa) :
    ∃ history, (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence (KuratowskiZF.interpretation hM)
      (Operation hM D enumeration) history kappa := by
  let env : Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Fin.cases D (fun _ => enumeration),fun _ => D⟩
  let schema : Project.BinarySchema 2 := {body := operation 2 3 1 0,freeClosed := operation_freeClosed ..}
  have he S A : schema.denote env S A ↔ Operation hM D enumeration S A :=
    operation_semantics hM _ _ _ _ _
  obtain ⟨history,hHistory⟩ := ZF.recursiveSequence_exists (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) env schema (by
      intro S _
      obtain ⟨A,hA,hUnique⟩ := operation_exists_unique hM D enumeration S
      exact ⟨A,(he S A).mpr hA,fun B hB => hUnique B ((he S B).mp hB)⟩) hk
  exact ⟨history,hHistory.1,fun i hi A hiA => by
    obtain ⟨S,hS,hOp⟩ := hHistory.2 i hi A hiA
    exact ⟨S,hS,(he S A).mp hOp⟩⟩

def Antichain (A : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A →
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q A → Compatible p q → p = q

def antichain {n : Nat} (A : Fin n) : Project.Formula 1 n :=
  .forallE (.imp (.mem (.bound 0) (.bound A.succ))
    (.forallE (.imp (.mem (.bound 0) (.bound A.succ.succ))
      (.imp (ConstructionCompatiblePlacement.compatible 1 0)
        (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))

theorem antichain_freeClosed {n : Nat} (A : Fin n) : (antichain A).FreeClosed := by
  simp -implicitDefEqProofs [antichain,Definitional.Formula.FreeClosed,
    ConstructionCompatiblePlacement.compatible_freeClosed,Project.Formula.extensionalEq]

theorem antichain_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (A : Fin n) :
    Project.Formula.satisfies env (antichain A) ↔ Antichain (env.bound A) := by
  simp only [antichain,Antichain,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCompatiblePlacement.compatible_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

private theorem compatible_symm {p q : M.Carrier .set} (h : Compatible p q) : Compatible q p :=
  fun x b c hb hc => (h x c b hc hb).symm

private theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF) {D F S x y : M.Carrier .set}
    (hF : FunctionOn D F) (hx : Selected hM F S x) (hy : Selected hM F S y) : x = y := by
  obtain ⟨i,hSi,hix,_⟩ := hx
  obtain ⟨j,hSj,hjy,_⟩ := hy
  have eq : j = i := (ModelTransfer.extensionality hM).eq_of_same_members j i
    (fun z => (hSj.2.2 z).trans (hSi.2.2 z).symm)
  exact ForcingConditionGraphs.function_unique hF hix (eq ▸ hjy)

private theorem operation_antichain (hM : FirstOrder.Theory.Models M nativeZF) {D K F S A : M.Carrier .set}
    (hF : FunctionOn K F) (hOp : Operation hM D F S A)
    (hPrior : ∀ p, Prior S p → ∀ q, Prior S q → Compatible p q → p = q) : Antichain A := by
  intro p hp q hq hpq
  obtain ⟨_,hp⟩ := (hOp p).mp hp
  obtain ⟨_,hq⟩ := (hOp q).mp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hPrior p hp q hq hpq
  · obtain ⟨_,_,_,hNo⟩ := hq
    exact False.elim (hNo p hp (compatible_symm hpq))
  · obtain ⟨_,_,_,hNo⟩ := hp
    exact False.elim (hNo q hq hpq)
  · exact selected_unique hM hF hp hq

section History
variable (hM : FirstOrder.Theory.Models M nativeZF) {D K F S : M.Carrier .set}
variable (hRec : (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence (KuratowskiZF.interpretation hM)
  (Operation hM D F) S K)
include hM hRec

private theorem row_subset {i A : M.Carrier .set} (hiA : PureKuratowski.PairMember M i A S) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset A D := by
  have hi := (hRec.1.2.2 i).mpr ⟨A,hiA⟩
  obtain ⟨T,_,hOp⟩ := hRec.2 i hi A hiA
  exact fun x hx => ((hOp x).mp hx).1

private theorem rows_mono {i j A B : M.Carrier .set}
    (hij : (Project.FirstOrderSemantics.reduct M).mem i j)
    (hiA : PureKuratowski.PairMember M i A S) (hjB : PureKuratowski.PairMember M j B S) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset A B := by
  obtain ⟨T,hT,hOp⟩ := hRec.2 j ((hRec.1.2.2 j).mpr ⟨B,hjB⟩) B hjB
  intro x hx
  exact (hOp x).mpr ⟨row_subset hM hRec hiA x hx,Or.inl
    ⟨i,A,(hT.2 i A).mpr ⟨hij,hiA⟩,hx⟩⟩

private theorem prior_antichain {T i : M.Carrier .set}
    (hT : (Project.FirstOrderSemantics.reduct M).IsRestrictionOf (KuratowskiZF.interpretation hM) T S i)
    (hi : (Project.FirstOrderSemantics.reduct M).IsOrdinal i)
    (hBefore : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j i →
      ∀ A, PureKuratowski.PairMember M j A S → Antichain A) :
    ∀ x, Prior T x → ∀ y, Prior T y → Compatible x y → x = y := by
  rintro x ⟨j,A,hjA,hx⟩ y ⟨l,B,hlB,hy⟩ hxy
  obtain ⟨hji,hjAS⟩ := (hT.2 j A).mp hjA
  obtain ⟨hli,hlBS⟩ := (hT.2 l B).mp hlB
  let hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  rcases Structure.IsOrdinal.trichotomy (ModelTransfer.extensionality hM) (hi.mem hji) (hi.mem hli)
    (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP j l) with hEq | hjl | hlj
  · have eq := (ModelTransfer.extensionality hM).eq_of_same_members j l hEq
    subst l
    have eAB := ForcingConditionGraphs.function_unique
      (ConstructionTowerIterationValidity.function_of_sequence hM hRec.1) hjAS hlBS
    subst B
    exact hBefore j hji A hjAS x hx y hy hxy
  · exact hBefore l hli B hlBS x (rows_mono hM hRec hjl hjAS hlBS x hx) y hy hxy
  · exact hBefore j hji A hjAS x hx y (rows_mono hM hRec hlj hlBS hjAS y hy) hxy

end History

def AllGood (S i : M.Carrier .set) : Prop :=
  ∀ j, (Project.FirstOrderSemantics.reduct M).mem j i →
    ∀ A, PureKuratowski.PairMember M j A S → Antichain A

def allGood {n : Nat} (S i : Fin n) : Project.Formula 1 n :=
  .forallE (.imp (.mem (.bound 0) (.bound i.succ))
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ 1 0)) (antichain 0))))

theorem allGood_freeClosed {n : Nat} (S i : Fin n) : (allGood S i).FreeClosed := by
  simp -implicitDefEqProofs [allGood,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,antichain_freeClosed]

theorem allGood_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (S i : Fin n) :
    Project.Formula.satisfies env (allGood S i) ↔ AllGood (env.bound S) (env.bound i) := by
  simp only [allGood,AllGood,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,antichain_semantics hM]
  rfl

/-- Definable counterexamples and native ordinal induction, not a host
well-founded induction on the model's ordinal elements. -/
theorem recursive_antichains (hM : FirstOrder.Theory.Models M nativeZF) {D K F S : M.Carrier .set}
    (hF : FunctionOn K F)
    (hRec : (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence (KuratowskiZF.interpretation hM)
      (Operation hM D F) S K) : AllGood S K := by
  let env : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => S,fun _ => D⟩
  let schema : Project.UnarySchema 1 := {body := allGood 1 0,freeClosed := allGood_freeClosed ..}
  have he i : schema.denote env i ↔ AllGood S i := allGood_semantics hM _ _ _
  apply hRec.1.1.induction (AllGood S)
  · obtain ⟨bad,hBad⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema.neg env K
    refine ⟨bad,fun i => (hBad i).trans (and_congr_right fun _ => ?_)⟩
    simp only [Project.UnarySchema.neg,Project.Formula.satisfies_neg_iff]
    exact not_congr (he i)
  · intro i hi hPrevious j hji A hjA
    obtain ⟨T,hT,hOp⟩ := hRec.2 j ((hRec.1.2.2 j).mpr ⟨A,hjA⟩) A hjA
    exact operation_antichain hM hF hOp (prior_antichain hM hRec hT (hi.mem hji) (hPrevious j hji))

/-- Actual maximal Cohen antichain from the source family's internal ordinal
enumeration. No maximality, enumeration or history is supplied as an oracle. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {D S w : M.Carrier .set} (hD : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p D → Condition S w p) :
    ∃ A, (Project.FirstOrderSemantics.reduct M).MemberSubset A D ∧ Antichain A ∧
      ∀ d, (Project.FirstOrderSemantics.reduct M).mem d D →
        ∃ a, (Project.FirstOrderSemantics.reduct M).mem a A ∧ Compatible d a := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨K,F,hK,hFn,hSurj⟩ := ExistingOrdinalEnumeration.ordinal_enum_l
    (ConstructionDirectedCardinality.models_zfc hM hChoice) pair D
  have hF := ((ForcingSupportSize.native_mapsTo hM K D F).mpr hFn).1
  obtain ⟨history,hRec⟩ := recursive_exists hM (D := D) (enumeration := F) hK
  have hGood := recursive_antichains hM hF hRec
  obtain ⟨range,hRange⟩ := ZF.exists_range_of_setFunction hZF pair hRec.1.2.1 hRec.1.2.2
  obtain ⟨A,hA⟩ := KP.exists_union (ZF.modelsKP hZF) range
  have he x : (Project.FirstOrderSemantics.reduct M).mem x A ↔ Prior history x := by
    constructor
    · intro hx
      obtain ⟨row,hrow,hxrow⟩ := (hA x).mp hx
      obtain ⟨i,hirow⟩ := (hRange row).mp hrow
      exact ⟨i,row,hirow,hxrow⟩
    · rintro ⟨i,row,hirow,hxrow⟩
      exact (hA x).mpr ⟨row,(hRange row).mpr ⟨i,hirow⟩,hxrow⟩
  have hId : (Project.FirstOrderSemantics.reduct M).IsRestrictionOf pair history history K :=
    ⟨hRec.1.2.1.1,fun i row => ⟨fun h => ⟨(hRec.1.2.2 i).mpr ⟨row,h⟩,h⟩,And.right⟩⟩
  refine ⟨A,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,row,hirow,hxrow⟩ := (he x).mp hx
    exact row_subset hM hRec hirow x hxrow
  · intro x hx y hy hxy
    exact prior_antichain hM hRec hId hK hGood x ((he x).mp hx) y ((he y).mp hy) hxy
  · intro d hd
    obtain ⟨i,hi,hid⟩ := hSurj d hd
    obtain ⟨row,hirow,_⟩ := (ConstructionTowerIterationValidity.function_of_sequence hM hRec.1).2 i hi
    obtain ⟨T,hT,hOp⟩ := hRec.2 i hi row hirow
    by_cases hOld : ∃ a, Prior T a ∧ Compatible d a
    · obtain ⟨a,⟨j,B,hjB,haB⟩,hda⟩ := hOld
      exact ⟨a,(he a).mpr ⟨j,B,((hT.2 j B).mp hjB).2,haB⟩,hda⟩
    · have hSelect : Selected hM F T d := ⟨i,hRec.1.restriction hi hT,hid,fun a ha hda => hOld ⟨a,ha,hda⟩⟩
      have hdrow := (hOp d).mpr ⟨hd,Or.inr hSelect⟩
      exact ⟨d,(he d).mpr ⟨i,row,hirow,hdrow⟩,(hD d hd).2.1⟩

/-- Full source common-lower-bound presentation, with an actual Cohen union
as the predensity witness. -/
theorem maximal_antichain (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {D S w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hD : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p D → Condition S w p) :
    ∃ A, (Project.FirstOrderSemantics.reduct M).MemberSubset A D ∧
      (∀ p, (Project.FirstOrderSemantics.reduct M).mem p A →
        ∀ q, (Project.FirstOrderSemantics.reduct M).mem q A → ∀ r, Condition S w r →
          (Project.FirstOrderSemantics.reduct M).MemberSubset p r →
          (Project.FirstOrderSemantics.reduct M).MemberSubset q r → p = q) ∧
      ∀ d, (Project.FirstOrderSemantics.reduct M).mem d D →
        ∃ a r, (Project.FirstOrderSemantics.reduct M).mem a A ∧ Condition S w r ∧
          (Project.FirstOrderSemantics.reduct M).MemberSubset d r ∧
          (Project.FirstOrderSemantics.reduct M).MemberSubset a r := by
  obtain ⟨A,hAD,hAnti,hPred⟩ := construct hM hChoice hD
  refine ⟨A,hAD,?_,?_⟩
  · intro p hp q hq r hr hpr hqr
    apply hAnti p hp q hq
    intro x b c hb hc
    obtain ⟨z,hz,hzp⟩ := hb
    obtain ⟨z',hz',hzq⟩ := hc
    exact hr.2.1 x b c ⟨z,hz,hpr z hzp⟩ ⟨z',hz',hqr z' hzq⟩
  · intro d hd
    obtain ⟨a,ha,hda⟩ := hPred d hd
    obtain ⟨r,hr,_,hdr,har⟩ := ConstructionCohenCompatibility.exists_union hM hw (hD d hd) (hD a (hAD a ha)) hda
    exact ⟨a,r,ha,hr,hdr,har⟩

def Result (D S w A : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).MemberSubset A D ∧
    (∀ p, (Project.FirstOrderSemantics.reduct M).mem p A →
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q A → ∀ r, Condition S w r →
        (Project.FirstOrderSemantics.reduct M).MemberSubset p r →
        (Project.FirstOrderSemantics.reduct M).MemberSubset q r → p = q) ∧
    ∀ d, (Project.FirstOrderSemantics.reduct M).mem d D →
      ∃ a r, (Project.FirstOrderSemantics.reduct M).mem a A ∧ Condition S w r ∧
        (Project.FirstOrderSemantics.reduct M).MemberSubset d r ∧
        (Project.FirstOrderSemantics.reduct M).MemberSubset a r

def result {n : Nat} (D S w A : Fin n) : Project.Formula 1 n :=
  let up : Fin n → Fin (n+3) := fun j => j.succ.succ.succ
  .conj (ProjectSyntax.encode id (Source.SetLanguage.subset A D))
    (.conj
      (.forallE (.imp (.mem (.bound 0) (.bound A.succ))
        (.forallE (.imp (.mem (.bound 0) (.bound A.succ.succ))
          (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 0))
            (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset 2 0))
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset 1 0))
                (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))))))
      (.forallE (.imp (.mem (.bound 0) (.bound D.succ))
        (.existsE (.existsE (.conj (.mem (.bound 1) (.bound (up A)))
          (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 0))
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset 2 0))
              (ProjectSyntax.encode id (Source.SetLanguage.subset 1 0))))))))))

theorem result_freeClosed {n : Nat} (D S w A : Fin n) : (result D S w A).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (D S w A : Fin n) :
    Project.Formula.satisfies env (result D S w A) ↔ Result (env.bound D) (env.bound S) (env.bound w) (env.bound A) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

/-- Source maximal_antichain at its actual Cohen consumer, retaining the
literal common-lower-bound quantifiers and actual internal set witnesses. -/
def sentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3
    (.imp (Project.Formula.isOmega (.bound 2))
      (.imp (.forallE (.imp (.mem (.bound 0) (.bound 1))
        (ProjectSyntax.encode id (ForcingCohenConditions.condition 2 3 0))))
        (.existsE (result 1 2 3 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,result_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) : (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),result_semantics hM]
  intro hw hD
  exact maximal_antichain hM hChoice hw hD

theorem kernel_certificate :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative sentence)) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp (models hL hChoice)

end PPAC.Migration.ForcingMaximalAntichain
