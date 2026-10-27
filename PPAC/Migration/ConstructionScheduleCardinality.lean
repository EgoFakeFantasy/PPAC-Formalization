/- Pinned CompleteRound.cardinal_le: size of ScheduleIndex(Request x K).
Consume the SAME actual WithTop singleton carrier and canonical collapse;
the ordinal, all places, schedule values and last stage remain unchanged.
Existing native injection/product/union constructors; no new order backend. -/
import PPAC.Migration.ConstructionOrdinalScheduleSyntax
import PPAC.Migration.ConstructionRequestCardinality

namespace PPAC.Migration.ConstructionScheduleCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
open ForcingWithTopCarrier (Empty Single)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Tagged (A zero one i code : M.Carrier .set) : Prop :=
  (Empty i ∧ PureKuratowski.Code M code zero zero) ∨
  ∃ p, (Project.FirstOrderSemantics.reduct M).mem p A ∧ Single i p ∧ PureKuratowski.Code M code one p


def tagged {m : Nat} (A zero one i code : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty i)) (PureKuratowskiProject.code (.bound
  code) (.bound zero) (.bound zero))) (.existsE (.conj (.mem (.bound (0 : Fin (m+1))) (.bound A.succ))
  (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.single i.succ (0 : Fin (m+1))))
  (PureKuratowskiProject.code (.bound code.succ) (.bound one.succ) (.bound (0 : Fin (m+1))))))))

theorem tagged_freeClosed {m : Nat} (A zero one i code : Fin m) :
    (tagged A zero one i code).FreeClosed := by
  simp -implicitDefEqProofs [tagged,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem tagged_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A zero one i code : Fin m) :
    Project.Formula.satisfies env (tagged A zero one i code) ↔ Tagged (env.bound A) (env.bound zero) (env.bound one) (env.bound i) (env.bound code) := by
  simp only [tagged,Tagged,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_disj_iff,ForcingWithTopCarrier.empty_semantics,ForcingWithTopCarrier.single_semantics,KuratowskiZF.code_correct hM]
  rfl


theorem tagged_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {A zero one i x y : M.Carrier .set}
    (hx : Tagged A zero one i x) (hy : Tagged A zero one i y) : x = y := by
  rcases hx with ⟨he,hx⟩ | ⟨p,hp,hs,hx⟩ <;> rcases hy with ⟨he',hy⟩ | ⟨q,hq,ht,hy⟩
  · exact KuratowskiZF.code_unique hM hx hy
  · exact False.elim (ForcingWithTopCarrier.single_nonempty ht he)
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hs he')
  · have eqp := ForcingWithTopCarrier.single_injective hs ht
    subst q
    exact KuratowskiZF.code_unique hM hx hy

theorem tagged_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {A zero one i j code : M.Carrier .set} (hne : zero ≠ one)
    (hi : Tagged A zero one i code) (hj : Tagged A zero one j code) : i = j := by
  rcases hi with ⟨he,hi⟩ | ⟨p,_,hs,hi⟩ <;> rcases hj with ⟨he',hj⟩ | ⟨q,_,ht,hj⟩
  · exact ForcingWithTopCarrier.empty_unique hM he he'
  · exact False.elim (hne (PureKuratowski.code_injective hi hj).1)
  · exact False.elim (hne (PureKuratowski.code_injective hj hi).1)
  · have eqp := (PureKuratowski.code_injective hi hj).2
    subst q
    exact ForcingWithTopCarrier.single_unique hM hs ht

theorem index_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu A I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hA : Small A mu) (hI : ForcingWithTopCarrier.Carrier A I) : Small I mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨zero,hzero,hzw⟩ := hw.1.1
  obtain ⟨one,hone,how⟩ := hw.1.2 zero hzw
  have hne : zero ≠ one := fun he => hzero zero (he.symm ▸ hone.predecessor_mem)
  obtain ⟨B,hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A w
  have hBSmall := ExistingCardinalBounds.infinite_union_two_l P hZF hw hmu
    ((ForcingSupportSize.native_small hM A mu).mp hA) hmu.2 hB
  obtain ⟨Raw,hRaw⟩ := ZF.exists_cartesianProduct hZF P w B
  have hRawSmall := ExistingCardinalBounds.infinite_product_l P hZF hw hmu hmu.2 hBSmall hRaw
  let schema : Project.BinarySchema 3 := {
    body := tagged 2 3 4 1 0
    freeClosed := tagged_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases A (Fin.cases zero (Fin.cases one Fin.elim0)), free := fun _ => zero }
  have he (i code) : schema.denote env i code ↔ Tagged A zero one i code :=
    tagged_semantics hM ((env.push i).push code) 2 3 4 1 0
  obtain ⟨F,hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF P schema env (source := I) (target := Raw)
    (by
      intro i hi
      rcases (hI i).mp hi with hempty | ⟨p,hp,hs⟩
      · obtain ⟨code,hcode⟩ := P.total zero zero
        exact ⟨code,(he i code).mpr (Or.inl ⟨hempty,hcode⟩)⟩
      · obtain ⟨code,hcode⟩ := P.total one p
        exact ⟨code,(he i code).mpr (Or.inr ⟨p,hp,hs,hcode⟩)⟩)
    (by intro i _ x y hx hy; exact tagged_unique hM ((he i x).mp hx) ((he i y).mp hy))
    (by
      intro i code _ hc
      rcases (he i code).mp hc with ⟨_,hcode⟩ | ⟨p,hp,_,hcode⟩
      · exact (hRaw code).mpr ⟨zero,hzw,zero,(hB zero).mpr (Or.inr hzw),hcode⟩
      · exact (hRaw code).mpr ⟨one,how,p,(hB p).mpr (Or.inl hp),hcode⟩)
    (by intro i j code _ _ hi hj; exact tagged_injective hM hne ((he i code).mp hi) ((he j code).mp hj))
  obtain ⟨bound,hBound⟩ := hRawSmall
  exact (ForcingSupportSize.native_small hM I mu).mpr (ZF.exists_compositionInjection hZF P hF hBound)

theorem bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hRequests : Small Requests mu) (hK : Small K mu)
    (hd : ConstructionOrdinalSchedule.Data hM Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last) :
    Small A mu ∧ Small I mu ∧ Small ordinal mu ∧ Small last mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  rcases hd with ⟨hOrdered,_,_,hInverse,_,_,_,_,_,_,_,_,_,hLastMembers,_⟩
  have hProduct : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct P A Requests K := by
    intro p
    exact (hOrdered.1.1 p).trans ⟨fun ⟨q,k,hq,hk,hcode⟩ => ⟨q,hq,k,hk,hcode⟩,
      fun ⟨q,hq,k,hk,hcode⟩ => ⟨q,k,hq,hk,hcode⟩⟩
  have hASmall := (ForcingSupportSize.native_small hM A mu).mpr
    (ExistingCardinalBounds.infinite_product_l P hZF hw hmu
      ((ForcingSupportSize.native_small hM Requests mu).mp hRequests)
      ((ForcingSupportSize.native_small hM K mu).mp hK) hProduct)
  have hISmall := index_small hM hw hmu hASmall hOrdered.1.2.1
  obtain ⟨F,hF⟩ := (ForcingSupportSize.native_small hM I mu).mp hISmall
  have hOrdinal := (ForcingSupportSize.native_small hM ordinal mu).mpr
    (ZF.exists_compositionInjection hZF P hInverse.1 hF)
  have hLast := ForcingSupportSize.small_subset hM
    (fun x hx => (hLastMembers x).mpr (Or.inl hx)) hOrdinal
  exact ⟨hASmall,hISmall,hOrdinal,hLast⟩

theorem exists_bounded_system (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M))
    {w D mul e zero one Requests K base mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu) (hKSmall : Small K mu)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hne : zero ≠ one) (hR : ConstructionRequestCarrier.Carrier w D mul e zero one Requests)
    (hbase : (Project.FirstOrderSemantics.reduct M).mem base Requests)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ A I top Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last,
      ConstructionOrdinalSchedule.Data hM Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last ∧
      Small Requests mu ∧ Small A mu ∧ Small I mu ∧ Small ordinal mu ∧ Small last mu := by
  obtain ⟨A,I,top,Schedule,Place,r,R,ordinal,collapse,inverse,ordSchedule,ordPlace,last,hd⟩ :=
    ConstructionOrdinalSchedule.exists_system hM hc hbase hK
  have hRequests := ConstructionRequestCardinality.data_cardinal_le hM hw hmu hpow hD hz ho hne hR
  exact ⟨A,I,top,Schedule,Place,r,R,ordinal,collapse,inverse,ordSchedule,ordPlace,last,
    hd,hRequests,bounds hM hw hmu hRequests hKSmall hd⟩

def boundSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 18 (.imp (Project.Formula.isOmega (.bound (0 : Fin 18))) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 18)) (.bound (1 :
    Fin 18))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (2 : Fin 18) (1 : Fin 18))) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (3 : Fin 18) (1 : Fin 18))) (.imp
    (ConstructionOrdinalScheduleSyntax.data (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18)
    (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18) (11 : Fin 18) (12 : Fin 18) (13 : Fin 18) (14 : Fin
    18) (15 : Fin 18) (16 : Fin 18) (17 : Fin 18)) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 18) (1 : Fin 18))) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (5 : Fin 18) (1 :
    Fin 18))) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (12 : Fin 18) (1 : Fin 18)))
    (ProjectSyntax.encode id (ForcingSupportSize.small (17 : Fin 18) (1 : Fin 18))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionOrdinalScheduleSyntax.data_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionOrdinalScheduleSyntax.data_semantics hM]
  exact fun hw hmu hR hK hd => bounds hM hw hmu hR hK hd

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 10 (.imp (ConstructionDirectedCardinality.choice ) (.imp
    (Project.Formula.isOmega (.bound (0 : Fin 10))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 10)) (.bound (9 : Fin 10))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (9 : Fin 10)) (.bound
    (9 : Fin 10)) (.bound (0 : Fin 10))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (1 : Fin
    10) (9 : Fin 10))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (7 : Fin 10) (9 : Fin 10)))
    (.imp (.mem (.bound (4 : Fin 10)) (.bound (0 : Fin 10))) (.imp (.mem (.bound (5 : Fin 10)) (.bound (0 :
    Fin 10))) (.imp (.neg (Project.Formula.extensionalEq (.bound (4 : Fin 10)) (.bound (5 : Fin 10)))) (.imp
    (ConstructionRequestCarrier.carrier (0 : Fin 10) (1 : Fin 10) (2 : Fin 10) (3 : Fin 10) (4 : Fin 10) (5
    : Fin 10) (6 : Fin 10)) (.imp (.mem (.bound (8 : Fin 10)) (.bound (6 : Fin 10))) (.imp (.existsE (.mem
    (.bound (0 : Fin 11)) (.bound (7 : Fin 10).succ))) (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionOrdinalScheduleSyntax.data (6 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (23)) (11 : Fin (23)) (10
    : Fin (23)) (8 : Fin 10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (23))
    (8 : Fin (23)) (7 : Fin (23)) (6 : Fin (23)) (5 : Fin (23)) (4 : Fin (23)) (3 : Fin (23)) (2 : Fin (23))
    (1 : Fin (23)) (0 : Fin (23))) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (ForcingSupportSize.small (12 : Fin (23)) (9 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (ForcingSupportSize.small (11 : Fin (23)) (9 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (ForcingSupportSize.small (5 : Fin (23)) (9 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (ProjectSyntax.encode id
    (ForcingSupportSize.small (0 : Fin (23)) (9 : Fin
    10).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedCardinality.choice_freeClosed,ConstructionRequestCarrier.carrier_freeClosed,
      Project.Formula.extensionalEq,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionOrdinalScheduleSyntax.data_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionRequestCarrier.carrier_semantics hM,
    ConstructionDirectedCardinality.choice_semantics hM,ConstructionOrdinalScheduleSyntax.data_semantics hM]
  exact fun hc hw hmu hpow hD hKS hz ho hne hR hbase hK =>
    exists_bounded_system hM hc hw hmu hpow hD hKS hz ho hne hR hbase hK

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionScheduleCardinality
