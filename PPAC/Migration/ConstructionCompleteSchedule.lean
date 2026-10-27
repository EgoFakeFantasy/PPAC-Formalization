/- Pinned CompleteRounds.CompleteRound.Index/schedule/place:403-418.
Construct ACTUAL full Request x K + top index carrier, actual schedule and
all designated positions. This file asserts carrier/graph/placement facts;
source well-order/ordinal indexing and size bounds are separate obligations. -/
import PPAC.Migration.ConstructionRequestCarrier

namespace PPAC.Migration.ConstructionCompleteSchedule
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (A base i q : M.Carrier .set) : Prop :=
  (Empty i ∧ q = base) ∨ ∃ p k, Single i p ∧ PureKuratowski.Code M p q k ∧
    (Project.FirstOrderSemantics.reduct M).mem p A

def Graph (I A base Schedule : M.Carrier .set) : Prop := ∀ i q,
  PureKuratowski.PairMember M i q Schedule ↔ (Project.FirstOrderSemantics.reduct M).mem i I ∧ Value A base i q

def Places (A Place : M.Carrier .set) : Prop := ∀ p i,
  PureKuratowski.PairMember M p i Place ↔ (Project.FirstOrderSemantics.reduct M).mem p A ∧ Single i p

theorem value_unique {A base i q r : M.Carrier .set} (hq : Value A base i q) (hr : Value A base i r) : q = r := by
  rcases hq with ⟨hq,eq⟩ | ⟨p,k,hp,hCode,_⟩
  · rcases hr with ⟨_,er⟩ | ⟨_,_,hs,_,_⟩
    · exact eq.trans er.symm
    · exact (ForcingWithTopCarrier.single_nonempty hs hq).elim
  · rcases hr with ⟨he,_⟩ | ⟨p',k',hp',hCode',_⟩
    · exact (ForcingWithTopCarrier.single_nonempty hp he).elim
    · have ep := ForcingWithTopCarrier.single_injective hp hp'
      subst p'
      exact (PureKuratowski.code_injective hCode hCode').1

theorem exists_places (hM : FirstOrder.Theory.Models M nativeZF) {A I : M.Carrier .set}
    (hI : ForcingWithTopCarrier.Carrier A I) :
    ∃ Place, Injection A I Place ∧ Places A Place := by
  let schema : Project.BinarySchema 0 := {
    body := ProjectSyntax.encode id (ForcingWithTopCarrier.single 0 1)
    freeClosed := ProjectSyntax.freeClosed id _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := { bound := Fin.elim0, free := fun _ => A }
  have he (p i) : schema.denote env p i ↔ Single i p := by
    simp only [Project.BinarySchema.denote,schema,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingWithTopCarrier.single_semantics (M := M)]
    rfl
  obtain ⟨Place,hPlace,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := A) (target := I) (by
      intro p hp
      obtain ⟨i,_,hi⟩ := ForcingWithTopCarrier.exists_embedding hM hI hp
      exact ⟨i,(he p i).mpr hi⟩) (by
      intro p _ i j hi hj
      exact ForcingWithTopCarrier.single_unique hM ((he p i).mp hi) ((he p j).mp hj)) (by
      intro p i hp hi
      exact (hI i).mpr (Or.inr ⟨p,hp,(he p i).mp hi⟩))
  have hMaps := (ForcingSupportSize.native_mapsTo hM A I Place).mpr hPlace
  have hP : Places A Place := fun p i => (hGraph p i).trans (and_congr_right fun _ => he p i)
  exact ⟨Place,⟨hMaps,fun p q i hp hq => ForcingWithTopCarrier.single_injective ((hP p i).mp hp).2 ((hP q i).mp hq).2⟩,hP⟩


def value {m : Nat} (A base i q : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty i)) (Project.Formula.extensionalEq
  (.bound q) (.bound base))) (.existsE (.existsE (.conj (ProjectSyntax.encode id
  (ForcingWithTopCarrier.single i.succ.succ (1 : Fin (m+2)))) (.conj (PureKuratowskiProject.code (.bound (1
  : Fin (m+2))) (.bound q.succ.succ) (.bound (0 : Fin (m+2)))) (.mem (.bound (1 : Fin (m+2))) (.bound
  A.succ.succ)))))))

theorem value_freeClosed {m : Nat} (A base i q : Fin m) :
    (value A base i q).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,PureKuratowskiProject.code]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A base i q : Fin m) :
    Project.Formula.satisfies env (value A base i q) ↔ Value (env.bound A) (env.bound base) (env.bound i) (env.bound q) := by
  simp only [Project.Formula.satisfies_disj_iff,value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.empty_semantics (M := M),ForcingWithTopCarrier.single_semantics (M := M),KuratowskiZF.code_correct hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def graph {m : Nat} (I A base Schedule : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ.succ (1 : Fin
  (m+2)) (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound I.succ.succ)) (value A.succ.succ
  base.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (I A base Schedule : Fin m) :
    (graph I A base Schedule).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A base Schedule : Fin m) :
    Project.Formula.satisfies env (graph I A base Schedule) ↔ Graph (env.bound I) (env.bound A) (env.bound base) (env.bound Schedule) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl


def places {m : Nat} (A Place : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Place.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound A.succ.succ)) (ProjectSyntax.encode id
  (ForcingWithTopCarrier.single (0 : Fin (m+2)) (1 : Fin (m+2))))))))

theorem places_freeClosed {m : Nat} (A Place : Fin m) :
    (places A Place).FreeClosed := by
  simp -implicitDefEqProofs [places,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem places_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A Place : Fin m) :
    Project.Formula.satisfies env (places A Place) ↔ Places (env.bound A) (env.bound Place) := by
  simp only [places,Places,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingWithTopCarrier.single_semantics (M := M)]
  rfl


/-- All underlying CompleteRound schedule/index/placement data. The chosen
well-order and ordinal iteration are not premises hidden in these fields. -/
def Data (Requests K A I top base Schedule Place : M.Carrier .set) : Prop :=
  ConstructionProbeLetters.Representatives Requests K A ∧ ForcingWithTopCarrier.Carrier A I ∧
    Empty top ∧ (Project.FirstOrderSemantics.reduct M).mem top I ∧ MapsTo I Requests Schedule ∧
    Graph I A base Schedule ∧ Injection A I Place ∧ Places A Place ∧
    PureKuratowski.PairMember M top base Schedule ∧
    (∀ q k, (Project.FirstOrderSemantics.reduct M).mem q Requests → (Project.FirstOrderSemantics.reduct M).mem k K →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i I ∧ Product Place q k i ∧
        PureKuratowski.PairMember M i q Schedule ∧ i ≠ top) ∧
    (∀ q, (Project.FirstOrderSemantics.reduct M).mem q Requests →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i I ∧ PureKuratowski.PairMember M i q Schedule ∧ i ≠ top) ∧
    (∀ q k l i, Product Place q k i → Product Place q l i → k = l) ∧
    ∀ other, MapsTo I Requests other → Graph I A base other → other = Schedule

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {Requests K base : M.Carrier .set}
    (hbase : (Project.FirstOrderSemantics.reduct M).mem base Requests)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ A I top Schedule Place, Data Requests K A I top base Schedule Place := by
  obtain ⟨A,hA⟩ := ConstructionProbeLetters.exists_representatives hM Requests K
  obtain ⟨I,hI⟩ := ForcingWithTopCarrier.exists_carrier hM A
  obtain ⟨top,hTop⟩ := ForcingWithTopCarrier.exists_empty hM
  have hTopI := (hI top).mpr (Or.inl hTop)
  let schema : Project.BinarySchema 2 := { body := value 2 3 1 0, freeClosed := value_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases A (fun _ => base), free := fun _ => base }
  have he (i q) : schema.denote env i q ↔ Value A base i q := value_semantics hM ((env.push i).push q) 2 3 1 0
  obtain ⟨Schedule,hSch,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := I) (target := Requests) (by
      intro i hi
      rcases (hI i).mp hi with hempty | ⟨p,hp,hSingle⟩
      · exact ⟨base,(he i base).mpr (Or.inl ⟨hempty,rfl⟩)⟩
      · obtain ⟨q,k,_,_,hCode⟩ := (hA p).mp hp
        exact ⟨q,(he i q).mpr (Or.inr ⟨p,k,hSingle,hCode,hp⟩)⟩) (by
      intro i _ q r hq hr
      exact value_unique ((he i q).mp hq) ((he i r).mp hr)) (by
      intro i q _ hq
      rcases (he i q).mp hq with ⟨_,heq⟩ | ⟨p,k,_,hCode,hp⟩
      · exact heq.symm ▸ hbase
      · obtain ⟨q',k',hq',_,hCode'⟩ := (hA p).mp hp
        have eq := (PureKuratowski.code_injective hCode hCode').1
        exact eq.symm ▸ hq')
  have hMaps := (ForcingSupportSize.native_mapsTo hM I Requests Schedule).mpr hSch
  have hG : Graph I A base Schedule := fun i q => (hGraph i q).trans (and_congr_right fun _ => he i q)
  obtain ⟨Place,hPlace,hPlaces⟩ := exists_places hM hI
  have hAt : ∀ q k, (Project.FirstOrderSemantics.reduct M).mem q Requests →
      (Project.FirstOrderSemantics.reduct M).mem k K →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i I ∧ Product Place q k i ∧
        PureKuratowski.PairMember M i q Schedule ∧ i ≠ top := by
    intro q k hq hk
    obtain ⟨p,hCode⟩ := KuratowskiZF.exists_code hM q k
    have hp := (hA p).mpr ⟨q,k,hq,hk,hCode⟩
    obtain ⟨i,hpi,_⟩ := hPlace.1.1.2 p hp
    have hi := hPlace.1.2 p i hpi
    have hSingle := ((hPlaces p i).mp hpi).2
    refine ⟨i,hi,⟨p,hCode,hpi⟩,(hG i q).mpr ⟨hi,Or.inr ⟨p,k,hSingle,hCode,hp⟩⟩,?_⟩
    intro hei
    exact ForcingWithTopCarrier.single_nonempty hSingle (hei.symm ▸ hTop)
  refine ⟨A,I,top,Schedule,Place,hA,hI,hTop,hTopI,hMaps,hG,hPlace,hPlaces,
    (hG top base).mpr ⟨hTopI,Or.inl ⟨hTop,rfl⟩⟩,hAt,?_,?_,?_⟩
  · intro q hq
    obtain ⟨k,hk⟩ := hK
    obtain ⟨i,hi,_,hqi,hne⟩ := hAt q k hq hk
    exact ⟨i,hi,hqi,hne⟩
  · intro q k l i hk hl
    obtain ⟨p,hp,hpi⟩ := hk
    obtain ⟨p',hp',hpi'⟩ := hl
    have ep := hPlace.2 p p' i hpi hpi'
    subst p'
    exact (PureKuratowski.code_injective hp hp').2
  · intro other hOther hOtherGraph
    exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM I Requests other).mp hOther).1.1 hSch.1.1
      (fun i q => (hOtherGraph i q).trans (hG i q).symm)

theorem exists_all (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e mark zero one K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hne : mark ≠ e)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ Requests node base A I top Schedule Place,
      ConstructionRequestCarrier.Carrier w D mul e zero one Requests ∧ MapsTo w D node ∧
      ConstructionRequestCarrier.ConstantNode w e node ∧ ConstructionProbePath.Path w D mul e zero e node ∧
      ConstructionRequestSchedule.ProbeCode zero e mark node base ∧
      (Project.FirstOrderSemantics.reduct M).mem base Requests ∧ zero ≠ one ∧
      Data Requests K A I top base Schedule Place ∧ ConstructionRequestSchedule.Requests Schedule w D mul e zero one ∧
      (∀ N mulN eN f q qN, (Project.FirstOrderSemantics.reduct M).mem q Requests →
        ConstructionRequestSchedule.Transport w D mul e zero one N mulN eN f q qN →
        ConstructionRequestCarrier.Element w N mulN eN zero one qN) ∧
      ∀ other, ConstructionRequestCarrier.Carrier w D mul e zero one other → other = Requests := by
  obtain ⟨Requests,node,base,hR,hNode,hConst,hPath,hCode,hbase,h01,hLegacy,hTransport,hUnique⟩ :=
    ConstructionRequestCarrier.exists_system hM hw hz hzw hone hm hmark hne
  obtain ⟨A,I,top,Schedule,Place,hData⟩ := exists_system hM hbase hK
  have hSch : MapsTo I Requests Schedule := hData.2.2.2.2.1
  exact ⟨Requests,node,base,A,I,top,Schedule,Place,hR,hNode,hConst,hPath,hCode,hbase,h01,hData,
    fun i q hq => hLegacy q (hSch.2 i q hq),hTransport,hUnique⟩

end PPAC.Migration.ConstructionCompleteSchedule
