/- Pinned MonoidRounds.WellOrdered / ScheduleIndex and CompleteRounds
place_not_isMax. Choose an INTERNAL order on the ACTUAL request product,
then extend that SAME carrier by its already constructed WithTop codes.
Reuse donor ordinal enumeration and native least-preimage/order-type kernels. -/
import PPAC.Migration.ConstructionCompleteScheduleSyntax
import PPAC.Migration.ExistingOrdinalEnumeration
import PPAC.Migration.ConstructionDirectedCardinality

namespace PPAC.Migration.ConstructionScheduleOrder
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Actual chosen source order on the Request x K product; object ZFC explicit. -/
theorem exists_product_order (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M)) (Requests K A : M.Carrier .set)
    (_hA : ConstructionProbeLetters.Representatives Requests K A) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A := by
  let N := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨κ,F,hκ,hF,hOnto⟩ := ExistingOrdinalEnumeration.ordinal_enum_l
    (ConstructionDirectedCardinality.models_zfc hM hc) I A
  obtain ⟨rank,hrank⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I hκ hF hOnto
  let env : SetTheory.Env N 1 := ⟨fun _ => rank,fun _ => A⟩
  obtain ⟨r,hr,hg⟩ := ZF.exists_setRelationOn_of_denote hZF I
    (Project.BinarySchema.transportedOrdinalMembership PureKuratowskiProject.convention) env A
  have rel x y : N.PairMember I x y r ↔ N.mem x A ∧ N.mem y A ∧
      ∃ a b, N.PairMember I x a rank ∧ N.PairMember I y b rank ∧ N.mem a b := by
    rw [hg x y,Project.Formula.denote_transportedOrdinalMembership_iff I]
  refine ⟨r,⟨⟨hr.1,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩⟩
  · intro x _ hx
    obtain ⟨_,_,a,b,ha,hb,hab⟩ := (rel x x).mp hx
    have eq := hrank.1.1.2 x a b ha hb
    subst b
    exact hκ.wellOrder.linear.irrefl a (hrank.1.output_mem_of_pairMember ha) hab
  · intro x hx y hy z hz hxy hyz
    obtain ⟨_,_,a,b,ha,hb,hab⟩ := (rel x y).mp hxy
    obtain ⟨_,_,b',c,hb',hc,hbc⟩ := (rel y z).mp hyz
    have eq := hrank.1.1.2 y b b' hb hb'
    subst b'
    exact (rel x z).mpr ⟨hx,hz,a,c,ha,hc,hκ.wellOrder.linear.trans
      a (hrank.1.output_mem_of_pairMember ha) b (hrank.1.output_mem_of_pairMember hb)
      c (hrank.1.output_mem_of_pairMember hc) hab hbc⟩
  · intro x hx y hy
    obtain ⟨a,ha,he⟩ := hrank.1.2.2 x hx
    obtain ⟨b,hb,hf⟩ := hrank.1.2.2 y hy
    rcases hκ.wellOrder.linear.compare a ha b hb with eq | lt | gt
    · have eq' := hZF.1.eq_of_same_members a b eq
      subst b
      have exy := hrank.2 x y a he hf
      subst y
      exact Or.inl (fun _ => Iff.rfl)
    · exact Or.inr (Or.inl ((rel x y).mpr ⟨hx,hy,a,b,he,hf,lt⟩))
    · exact Or.inr (Or.inr ((rel y x).mpr ⟨hy,hx,b,a,hf,he,gt⟩))
  · intro X hX hne
    let schema : Project.UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention .newest (.bound 1) (.bound 3))) }
    let ρ : SetTheory.Env N 2 := ⟨Fin.cases X (fun _ => rank),fun _ => X⟩
    obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema ρ κ
    have hb a : N.mem a B ↔ N.mem a κ ∧ ∃ x, N.mem x X ∧ N.PairMember I x a rank := by
      rw [hB a]
      simp only [schema,Project.Formula.satisfies_exists_iff,
        Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
        Project.Formula.satisfies_orderedPairMem_iff I]
      rfl
    obtain ⟨x,hx⟩ := hne
    obtain ⟨a,ha,he⟩ := hrank.1.2.2 x (hX x hx)
    obtain ⟨a,ha,hmin⟩ := hκ.wellOrder.least B (fun a ha => ((hb a).mp ha).1)
      ⟨a,(hb a).mpr ⟨ha,x,hx,he⟩⟩
    obtain ⟨_,x,hx,he⟩ := (hb a).mp ha
    refine ⟨x,hx,?_⟩
    intro y hy
    obtain ⟨b,hbκ,hf⟩ := hrank.1.2.2 y (hX y hy)
    rcases hmin b ((hb b).mpr ⟨hbκ,y,hy,hf⟩) with eq | lt
    · have eq' := hZF.1.eq_of_same_members a b eq
      subst b
      have exy := hrank.2 x y a he hf
      subst y
      exact Or.inl (fun _ => Iff.rfl)
    · exact Or.inr ((rel x y).mpr ⟨hX x hx,hX y hy,a,b,he,hf,lt⟩)

def Lt (r x y : M.Carrier .set) : Prop :=
  (¬ Empty x ∧ Empty y) ∨ ∃ p q, Single x p ∧ Single y q ∧ PureKuratowski.PairMember M p q r

def lt {m : Nat} (r x y : Fin m) : Project.Formula 1 m :=
  .disj (.conj (.neg (ProjectSyntax.encode id (ForcingWithTopCarrier.empty x)))
    (ProjectSyntax.encode id (ForcingWithTopCarrier.empty y)))
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.single x.succ.succ 1))
      (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.single y.succ.succ 0))
        (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ 1 0))))))

theorem lt_freeClosed {m : Nat} (r x y : Fin m) : (lt r x y).FreeClosed := by
  simp -implicitDefEqProofs [lt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem lt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (r x y : Fin m) :
    Project.Formula.satisfies env (lt r x y) ↔ Lt (env.bound r) (env.bound x) (env.bound y) := by
  simp only [lt,Lt,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.empty_semantics,
    ForcingWithTopCarrier.single_semantics,KuratowskiZF.source_edge]
  rfl

/-- Extend the actual chosen product order to the SAME accepted WithTop carrier. -/
theorem exists_index_order (hM : FirstOrder.Theory.Models M nativeZF)
    {A I r : M.Carrier .set} (hI : ForcingWithTopCarrier.Carrier A I)
    (hr : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A) :
    ∃ R, (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) R I ∧
      ∀ x y, PureKuratowski.PairMember M x y R ↔
        (Project.FirstOrderSemantics.reduct M).mem x I ∧ (Project.FirstOrderSemantics.reduct M).mem y I ∧ Lt r x y := by
  let N := Project.FirstOrderSemantics.reduct M
  let J := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  let schema : Project.BinarySchema 1 := { body := lt 2 1 0, freeClosed := lt_freeClosed _ _ _ }
  let env : SetTheory.Env N 1 := ⟨fun _ => r,fun _ => r⟩
  have he x y : schema.denote env x y ↔ Lt r x y := lt_semantics hM ((env.push x).push y) 2 1 0
  obtain ⟨R,hR,hg⟩ := ZF.exists_setRelationOn_of_denote hZF J schema env I
  have rel x y : PureKuratowski.PairMember M x y R ↔ N.mem x I ∧ N.mem y I ∧ Lt r x y :=
    (hg x y).trans (and_congr_right fun _ => and_congr_right fun _ => he x y)
  have coe {x y p q} (hx : Single (M := M) x p) (hy : Single y q) :
      Lt r x y ↔ PureKuratowski.PairMember M p q r := by
    constructor
    · rintro (⟨_,hempty⟩ | ⟨p',q',hp,hq,he⟩)
      · exact (ForcingWithTopCarrier.single_nonempty hy hempty).elim
      · have ep := ForcingWithTopCarrier.single_injective hx hp
        have eq := ForcingWithTopCarrier.single_injective hy hq
        exact ep.symm ▸ eq.symm ▸ he
    · exact fun h => Or.inr ⟨p,q,hx,hy,h⟩
  refine ⟨R,⟨⟨hR.1,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩,rel⟩
  · intro x hx hxx
    rcases (hI x).mp hx with hx | ⟨p,hp,hs⟩
    · rcases ((rel x x).mp hxx).2.2 with h | ⟨_,_,h,_,_⟩
      · exact h.1 hx
      · exact ForcingWithTopCarrier.single_nonempty h hx
    · exact hr.linear.2.1.1 p hp ((coe hs hs).mp ((rel x x).mp hxx).2.2)
  · intro x hx y hy z hz hxy hyz
    have hxy' := ((rel x y).mp hxy).2.2
    have hyz' := ((rel y z).mp hyz).2.2
    apply (rel x z).mpr
    refine ⟨hx,hz,?_⟩
    rcases hxy' with ⟨hnx,hey⟩ | ⟨p,q,hp,hq,hpq⟩
    · rcases hyz' with ⟨hny,_⟩ | ⟨_,_,hs,_,_⟩
      · exact (hny hey).elim
      · exact (ForcingWithTopCarrier.single_nonempty hs hey).elim
    · rcases hyz' with ⟨_,hez⟩ | ⟨q',t,hq',ht,hqt⟩
      · exact Or.inl ⟨ForcingWithTopCarrier.single_nonempty hp,hez⟩
      · have eq := ForcingWithTopCarrier.single_injective hq hq'
        subst q'
        have memA {v a} (hv : N.mem v I) (hs : Single v a) : N.mem a A := by
          rcases (hI v).mp hv with he | ⟨b,hb,hs'⟩
          · exact (ForcingWithTopCarrier.single_nonempty hs he).elim
          · exact (ForcingWithTopCarrier.single_injective hs hs').symm ▸ hb
        exact Or.inr ⟨p,t,hp,ht,hr.linear.2.1.2 p (memA hx hp) q (memA hy hq) t (memA hz ht) hpq hqt⟩
  · intro x hx y hy
    rcases (hI x).mp hx with he | ⟨p,hp,hs⟩
    · rcases (hI y).mp hy with he' | ⟨q,_,ht⟩
      · have eq := ForcingWithTopCarrier.empty_unique hM he he'
        subst y
        exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr (Or.inr ((rel y x).mpr ⟨hy,hx,Or.inl ⟨ForcingWithTopCarrier.single_nonempty ht,he⟩⟩))
    · rcases (hI y).mp hy with he | ⟨q,hq,ht⟩
      · exact Or.inr (Or.inl ((rel x y).mpr ⟨hx,hy,Or.inl ⟨ForcingWithTopCarrier.single_nonempty hs,he⟩⟩))
      · rcases hr.linear.2.2 p hp q hq with eq | lt' | gt'
        · have eq' := hZF.1.eq_of_same_members p q eq
          subst q
          have eq'' := ForcingWithTopCarrier.single_unique hM hs ht
          subst y
          exact Or.inl (fun _ => Iff.rfl)
        · exact Or.inr (Or.inl ((rel x y).mpr ⟨hx,hy,(coe hs ht).mpr lt'⟩))
        · exact Or.inr (Or.inr ((rel y x).mpr ⟨hy,hx,(coe ht hs).mpr gt'⟩))
  · intro X hX hne
    let schema : Project.UnarySchema 1 := {
      body := .existsE (.conj (.mem .newest (.bound 2))
        (ProjectSyntax.encode id (ForcingWithTopCarrier.single 0 1)))
      freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
    let ρ : SetTheory.Env N 1 := ⟨fun _ => X,fun _ => X⟩
    obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema ρ A
    have hb p : N.mem p B ↔ N.mem p A ∧ ∃ x, N.mem x X ∧ Single (M := M) x p := by
      rw [hB p]
      simp only [schema,Project.Formula.satisfies_exists_iff,
        Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
        GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.single_semantics]
      rfl
    by_cases hn : ∃ p, N.mem p B
    · obtain ⟨p,hp,hmin⟩ := hr.least B (fun p hp => ((hb p).mp hp).1) hn
      obtain ⟨hpA,x,hx,hs⟩ := (hb p).mp hp
      refine ⟨x,hx,?_⟩
      intro y hy
      rcases (hI y).mp (hX y hy) with he | ⟨q,hq,ht⟩
      · exact Or.inr ((rel x y).mpr ⟨hX x hx,hX y hy,Or.inl ⟨ForcingWithTopCarrier.single_nonempty hs,he⟩⟩)
      · rcases hmin q ((hb q).mpr ⟨hq,y,hy,ht⟩) with eq | hlt
        · have eq' := hZF.1.eq_of_same_members p q eq
          subst q
          have eq'' := ForcingWithTopCarrier.single_unique hM hs ht
          subst y
          exact Or.inl (fun _ => Iff.rfl)
        · exact Or.inr ((rel x y).mpr ⟨hX x hx,hX y hy,(coe hs ht).mpr hlt⟩)
    · obtain ⟨x,hx⟩ := hne
      have all_empty y (hy : N.mem y X) : Empty (M := M) y := by
        rcases (hI y).mp (hX y hy) with he | ⟨q,hq,ht⟩
        · exact he
        · exact (hn ⟨q,(hb q).mpr ⟨hq,y,hy,ht⟩⟩).elim
      refine ⟨x,hx,?_⟩
      intro y hy
      have eq := ForcingWithTopCarrier.empty_unique hM (all_empty x hx) (all_empty y hy)
      subst y
      exact Or.inl (fun _ => Iff.rfl)

/-- All fields refer to the SAME actual exhaustive Schedule and WithTop carrier. -/
def OrderedData (hM : FirstOrder.Theory.Models M nativeZF)
    (Requests K A I top base Schedule Place r R ordinal : M.Carrier .set) : Prop :=
  ConstructionCompleteSchedule.Data Requests K A I top base Schedule Place ∧
    (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A ∧
    (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) R I ∧
    (∀ x y, PureKuratowski.PairMember M x y R ↔
      (Project.FirstOrderSemantics.reduct M).mem x I ∧ (Project.FirstOrderSemantics.reduct M).mem y I ∧ Lt r x y) ∧
    (∀ x, (Project.FirstOrderSemantics.reduct M).mem x I → x ≠ top → PureKuratowski.PairMember M x top R) ∧
    (∀ x, ¬ PureKuratowski.PairMember M top x R) ∧
    (∀ q k, (Project.FirstOrderSemantics.reduct M).mem q Requests → (Project.FirstOrderSemantics.reduct M).mem k K →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i I ∧ ForcingDiagramOrder.Product Place q k i ∧
        PureKuratowski.PairMember M i q Schedule ∧ PureKuratowski.PairMember M i top R) ∧
    (Project.FirstOrderSemantics.reduct M).IsWellOrderType (KuratowskiZF.interpretation hM) R I ordinal ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinal ordinal ∧
    (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) I ordinal

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M)) {Requests K base : M.Carrier .set}
    (hbase : (Project.FirstOrderSemantics.reduct M).mem base Requests)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K) :
    ∃ A I top Schedule Place r R ordinal,
      OrderedData hM Requests K A I top base Schedule Place r R ordinal := by
  obtain ⟨A,I,top,Schedule,Place,hd⟩ := ConstructionCompleteSchedule.exists_system hM hbase hK
  have hd' := hd
  rcases hd' with ⟨hA,hI,hTop,hTopI,_,_,_,_,_,hAt,_,_,_⟩
  obtain ⟨r,hr⟩ := exists_product_order hM hc Requests K A hA
  obtain ⟨R,hR,hRel⟩ := exists_index_order hM hI hr
  have before (x) (hx : (Project.FirstOrderSemantics.reduct M).mem x I) (hne : x ≠ top) :
      PureKuratowski.PairMember M x top R := by
    have he : ¬ Empty (M := M) x := fun he => hne (ForcingWithTopCarrier.empty_unique hM he hTop)
    exact (hRel x top).mpr ⟨hx,hTopI,Or.inl ⟨he,hTop⟩⟩
  have not_after (x) : ¬ PureKuratowski.PairMember M top x R := by
    intro hx
    rcases ((hRel top x).mp hx).2.2 with ⟨h,_⟩ | ⟨_,_,h,_,_⟩
    · exact h hTop
    · exact ForcingWithTopCarrier.single_nonempty h hTop
  obtain ⟨ordinal,hType,_⟩ := ZF.wellOrderType_existsUnique (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hR
  refine ⟨A,I,top,Schedule,Place,r,R,ordinal,hd,hr,hR,hRel,before,not_after,?_,hType,
    hType.isOrdinal (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hR,
    hType.equinumerous (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hR⟩
  intro q k hq hk
  obtain ⟨i,hi,hpi,hsch,hne⟩ := hAt q k hq hk
  exact ⟨i,hi,hpi,hsch,before i hi hne⟩

end PPAC.Migration.ConstructionScheduleOrder
