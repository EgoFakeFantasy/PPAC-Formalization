/- Existing completed YesMetaZFC 7979336 Choice.lean:79-189, copied with
unchanged theorem types and proof bodies except the Hartogs reference.
The pinned Hartogs body below replaces its sole automation call by explicit
successor extensionality, avoiding three fresh native Bool dependencies. Actual consumer: the chosen
well-order of CompleteRounds Request x K. Object ZFC stays explicit. -/
import PPAC.Migration.ExistingSmallUnion
import YesMetaZFC.SetTheory.Card.Aleph.Hartogs

namespace PPAC.Migration.ExistingOrdinalEnumeration
open YesMetaZFC SetTheory
open SetTheory.Definitional.Project
open ExistingSmallUnion (models_zf_l selector_l)
universe u
variable {M : Structure.{u}} (h : M.Models ZFC)
include h

section Hartogs
open SetTheory.ZF
omit h in
-- BEGIN NATIVE Hartogs.Exists
theorem exists_hartogsNumber_kernel
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (source : ℳ.Domain) :
    ∃ hartogs, ℳ.IsHartogsNumber 𝕀 hartogs source := by
  rcases exists_powerSet hZF source with
    ⟨carrierPower, hCarrierPower⟩
  rcases exists_cartesianProduct hZF 𝕀 source source with
    ⟨sourceProduct, hSourceProduct⟩
  rcases exists_powerSet hZF sourceProduct with
    ⟨relationPower, hRelationPower⟩
  rcases exists_cartesianProduct hZF 𝕀
      carrierPower relationPower with
    ⟨codeSpace, hCodeSpace⟩
  let sourceEnv : Env ℳ 1 := {
    bound := fun _ => source
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases separation_exists_d hZF (Definitional.Project.UnarySchema.hartogsWellOrderCodeMembership 𝒞)
      sourceEnv codeSpace with
    ⟨wellOrderCodes, hWellOrderCodes⟩
  have hCodeMembership (code : ℳ.Domain) :
      ℳ.mem code wellOrderCodes ↔
        ℳ.mem code codeSpace ∧
          ℳ.IsHartogsWellOrderCode 𝕀 code source := by
    rw [hWellOrderCodes code]
    change (ℳ.mem code codeSpace ∧
        Definitional.Project.Formula.satisfies (sourceEnv.push code) (Definitional.Project.Formula.isHartogsWellOrderCode 𝒞
            Definitional.Project.Term.newest (Definitional.Project.Term.bound 1))) ↔ _
    rw [Definitional.Project.Formula.satisfies_isHartogsWellOrderCode_iff
      𝕀]
    simp only [Definitional.Project.Term.eval_bound_one_push]
    rfl
  have hSuccessorTotal :
      ∀ code, ℳ.mem code wellOrderCodes →
        ∃ successor, (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
            sourceEnv code successor := by
    intro code hCode
    rcases (hCodeMembership code).mp hCode |>.2 with
      ⟨carrier, relation, hCodePair, hCarrierSubset, hOrder⟩
    rcases wellOrderType_existsUnique hZF 𝕀 hOrder with
      ⟨ordinal, hType, _⟩
    rcases KP.exists_successor (modelsKP hZF) ordinal with
      ⟨successor, hSuccessor⟩
    refine ⟨successor, (Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
        𝕀 hZF.1 sourceEnv code successor).mpr ?_⟩
    exact ⟨carrier, relation, ordinal,
      hCodePair, hCarrierSubset, hOrder, hType, hSuccessor⟩
  have hSuccessorUnique :
      ∀ code, ℳ.mem code wellOrderCodes →
        ∀ first second, (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
              sourceEnv code first → (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
              sourceEnv code second →
              first = second := by
    intro code _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hFirst hSecond
    rcases hFirst with
      ⟨firstCarrier, firstRelation, firstOrdinal,
        hFirstCode, _, hFirstOrder, hFirstType, hFirstSuccessor⟩
    rcases hSecond with
      ⟨secondCarrier, secondRelation, secondOrdinal,
        hSecondCode, _, _, hSecondType, hSecondSuccessor⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hCarrierEq, hRelationEq⟩
    subst secondCarrier
    subst secondRelation
    rcases wellOrderType_existsUnique hZF 𝕀 hFirstOrder with
      ⟨selected, _, hTypeUnique⟩
    have hFirstOrdinalEq := hTypeUnique firstOrdinal hFirstType
    have hSecondOrdinalEq := hTypeUnique secondOrdinal hSecondType
    subst firstOrdinal
    subst secondOrdinal
    exact hZF.1.eq_of_same_members first second
      (fun x => (hFirstSuccessor x).trans (hSecondSuccessor x).symm)
  rcases exists_functionalImageOn hZF (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞)
      sourceEnv wellOrderCodes
      hSuccessorTotal hSuccessorUnique with
    ⟨successors, hSuccessors⟩
  rcases KP.exists_union (modelsKP hZF) successors with
    ⟨hartogs, hHartogsUnion⟩
  have hSuccessorOrdinal :
      ∀ successor, ℳ.mem successor successors →
        ℳ.IsOrdinal successor := by
    intro successor hSuccessor
    rcases (hSuccessors successor).mp hSuccessor with
      ⟨code, hCode, hValue⟩
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hValue
    rcases hValue with
      ⟨carrier, relation, ordinal, _,
        _, hOrder, hType, hOrdinalSuccessor⟩
    exact KP.successor_isOrdinal (modelsKP hZF) (hType.isOrdinal hZF 𝕀 hOrder) hOrdinalSuccessor
  have hHartogsOrdinal : ℳ.IsOrdinal hartogs :=
    Structure.IsOrdinal.of_union (modelsKP hZF)
      hHartogsUnion hSuccessorOrdinal
  have hForward :
      ∀ α, ℳ.IsOrdinal α →
        ℳ.CardinalLessOrEqual 𝕀 α source →
          ℳ.mem α hartogs := by
    intro α hα hαSource
    rcases hαSource with ⟨function, hInjection⟩
    rcases exists_wellOrderRealization_of_ordinalInjection
        hZF 𝕀 hα hInjection with
      ⟨carrier, relation, hCarrierSubset,
        hRelationOn, hOrder, hType⟩
    have hRelationSubsetProduct :
        ℳ.MemberSubset relation sourceProduct := by
      intro pair hPair
      rcases hRelationOn.1 pair hPair with
        ⟨left, right, hCode⟩
      have hPairMember :
          ℳ.PairMember 𝕀 left right relation :=
        ⟨pair, hCode, hPair⟩
      have hCoordinates := hRelationOn.2 left right hPairMember
      exact (hSourceProduct pair).mpr
        ⟨left, hCarrierSubset left hCoordinates.1,
          right, hCarrierSubset right hCoordinates.2, hCode⟩
    rcases 𝕀.total carrier relation with
      ⟨code, hCodePair⟩
    have hCodeSpaceMember : ℳ.mem code codeSpace := by
      apply (hCodeSpace code).mpr
      exact ⟨carrier, (hCarrierPower carrier).mpr hCarrierSubset,
        relation, (hRelationPower relation).mpr hRelationSubsetProduct,
        hCodePair⟩
    have hCodeMember : ℳ.mem code wellOrderCodes := (hCodeMembership code).mpr
        ⟨hCodeSpaceMember,
          carrier, relation, hCodePair, hCarrierSubset, hOrder⟩
    rcases KP.exists_successor (modelsKP hZF) α with
      ⟨successor, hSuccessor⟩
    have hSuccessorValue : (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
          sourceEnv code successor := (Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
        𝕀 hZF.1 sourceEnv code successor).mpr
          ⟨carrier, relation, α,
            hCodePair, hCarrierSubset, hOrder, hType, hSuccessor⟩
    have hSuccessorMember : ℳ.mem successor successors := (hSuccessors successor).mpr
        ⟨code, hCodeMember, hSuccessorValue⟩
    exact (hHartogsUnion α).mpr
      ⟨successor, hSuccessorMember, (hSuccessor α).mpr <| Or.inr fun _ => Iff.rfl⟩
  have hBackward :
      ∀ α, ℳ.IsOrdinal α →
        ℳ.mem α hartogs →
          ℳ.CardinalLessOrEqual 𝕀 α source := by
    intro α hα hαHartogs
    rcases (hHartogsUnion α).mp hαHartogs with
      ⟨successor, hSuccessorMember, hαSuccessor⟩
    rcases (hSuccessors successor).mp hSuccessorMember with
      ⟨code, _, hSuccessorValue⟩
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hSuccessorValue
    rcases hSuccessorValue with
      ⟨carrier, relation, ordinal, _,
        hCarrierSubset, hOrder, hType, hSuccessor⟩
    have hOrdinal : ℳ.IsOrdinal ordinal :=
      hType.isOrdinal hZF 𝕀 hOrder
    have hOrdinalCarrier :
        ℳ.CardinalLessOrEqual 𝕀 ordinal carrier := by
      rcases (hType.equinumerous hZF 𝕀 hOrder).symm hZF 𝕀 with
        ⟨function, hFunction⟩
      exact ⟨function, hFunction.1⟩
    rcases exists_inclusionInjection hZF 𝕀 hCarrierSubset with
      ⟨carrierToSource, hCarrierToSource⟩
    rcases hOrdinalCarrier with
      ⟨ordinalToCarrier, hOrdinalToCarrier⟩
    rcases exists_compositionInjection hZF 𝕀
        hOrdinalToCarrier hCarrierToSource with
      ⟨ordinalToSource, hOrdinalToSource⟩
    rcases (hSuccessor α).mp hαSuccessor with
      hαOrdinal | hSame
    · have hαSubsetOrdinal : ℳ.MemberSubset α ordinal :=
        hOrdinal.transitive α hαOrdinal
      rcases exists_inclusionInjection hZF 𝕀 hαSubsetOrdinal with
        ⟨αToOrdinal, hαToOrdinal⟩
      rcases exists_compositionInjection hZF 𝕀
          hαToOrdinal hOrdinalToSource with
        ⟨αToSource, hαToSource⟩
      exact ⟨αToSource, hαToSource⟩
    · have hαEq :=
        hZF.1.eq_of_same_members α ordinal hSame
      subst ordinal
      exact ⟨ordinalToSource, hOrdinalToSource⟩
  exact ⟨hartogs, hHartogsOrdinal, fun α hα =>
    ⟨hBackward α hα, hForward α hα⟩⟩
-- END NATIVE Hartogs.Exists
end Hartogs

-- BEGIN DONOR Choice.OrdinalEnumeration
section Syntax
omit h

def Rem_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S F T : M.Domain) : Prop :=
  ∀ x, M.mem x T ↔ M.mem x S ∧ ¬ ∃ i, M.PairMember I i x F

def rem_m (𝒞 : OrderedPairConvention) {n} (S F T : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest T.weaken) (.conj (.mem .newest S.weaken)
    (.neg (.existsE (Formula.orderedPairMem 𝒞 .newest (.bound 1) F.weaken.weaken)))))
derive_free_closed rem_m

theorem rem_sat_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    {n} (ρ : Env M n) (S F T : Term n) :
    Formula.satisfies ρ (rem_m 𝒞 S F T) ↔ Rem_d I (S.eval ρ) (F.eval ρ) (T.eval ρ) := by
  simp only [rem_m, Rem_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

def Enum_step_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S C a F x : M.Domain) : Prop :=
  ∃ T, Rem_d I S F T ∧ ((M.mem x T ∧ M.PairMember I T x C) ∨ ((∀ y, ¬ M.mem y T) ∧ x = a))

def enum_step_m (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE (.conj (rem_m 𝒞 (.bound 5) (.bound 2) .newest)
    (.disj (.conj (.mem (.bound 1) .newest) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4)))
      (.conj (.forallE (.neg (.mem .newest (.bound 1)))) (Formula.extensionalEq (.bound 1) (.bound 3)))))

theorem enum_step_sat_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) (ρ : Env M 3) (F x : M.Domain) :
    (enum_step_m 𝒞).denote ρ F x ↔ Enum_step_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) F x := by
  simp only [enum_step_m, BinarySchema.denote, Enum_step_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, rem_sat_l I,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE]
  rfl

end Syntax

/-- 每个集合是某个内部序数的集合编码满射像；空集也由零长度枚举统一处理。 -/
theorem ordinal_enum_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ κ F, M.IsOrdinal κ ∧ M.IsSetFunctionFromTo I F κ S ∧ M.IsSetSurjectiveOnto I F κ S := by
  classical
  let hZF := models_zf_l h
  by_cases hn : ∃ a, M.mem a S
  · obtain ⟨a, ha⟩ := hn
    obtain ⟨C, hC⟩ := selector_l h I S
    let ρ : Env M 3 := ((⟨fun _ => S, fun _ => S⟩ : Env M 1).push C).push a
    have hs F x : (enum_step_m 𝒞).denote ρ F x ↔ Enum_step_d I S C a F x :=
      enum_step_sat_l I h.1 ρ F x
    have hop : M.IsClassFunctionOnTransfiniteSequences I ((enum_step_m 𝒞).denote ρ) := by
      intro F _
      let φ : UnarySchema 1 := {
        body := .neg (.existsE (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 2))) }
      obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ (⟨fun _ => F, fun _ => F⟩ : Env M 1) S
      have ht : Rem_d I S F T := by
        intro x
        rw [hT x]
        simp only [φ, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
          Formula.satisfies_orderedPairMem_iff I]
        rfl
      have hu {V} (hv : Rem_d I S F V) : V = T :=
        h.1.eq_of_same_members V T (fun x => (hv x).trans (ht x).symm)
      by_cases hn : ∃ x, M.mem x T
      · obtain ⟨x, hx, hc, he⟩ := hC T (fun x hx => ((ht x).mp hx).1) hn
        refine ⟨x, (hs F x).mpr ⟨T, ht, Or.inl ⟨hx, hc⟩⟩, fun y hy => ?_⟩
        obtain ⟨V, hv, hy⟩ := (hs F y).mp hy
        have := hu hv; subst V
        exact hy.elim (fun hy => he y hy.1 hy.2) (fun hy => False.elim (hy.1 x hx))
      · refine ⟨a, (hs F a).mpr ⟨T, ht, Or.inr ⟨fun x hx => hn ⟨x, hx⟩, rfl⟩⟩,
          fun y hy => ?_⟩
        obtain ⟨V, hv, hy⟩ := (hs F y).mp hy
        have := hu hv; subst V
        exact hy.elim (fun hy => False.elim (hn ⟨y, hy.1⟩)) And.right
    obtain ⟨κ, hκ⟩ := exists_hartogsNumber_kernel hZF I S
    obtain ⟨F, hF⟩ := ZF.recursiveSequence_exists hZF I ρ (enum_step_m 𝒞) hop hκ.1
    have step i x (hi : M.PairMember I i x F) :
        ∃ f, M.IsRestrictionOf I f F i ∧ Enum_step_d I S C a f x := by
      obtain ⟨f, hf, hx⟩ := hF.2 i ((hF.1.2.2 i).mpr ⟨x, hi⟩) x hi
      exact ⟨f, hf, (hs f x).mp hx⟩
    have hf : M.IsSetFunctionFromTo I F κ S := by
      refine ⟨hF.1.2.1, hF.1.2.2, fun i hi => ?_⟩
      obtain ⟨x, hx⟩ := (hF.1.2.2 i).mp hi
      obtain ⟨f, _, T, ht, hx'⟩ := step i x hx
      refine ⟨x, ?_, hx⟩
      exact hx'.elim (fun k => ((ht x).mp k.1).1) (fun k => k.2 ▸ ha)
    refine ⟨κ, F, hκ.1, hf, ?_⟩
    apply Classical.byContradiction
    intro hn
    apply hκ.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    refine ⟨F, hf, fun i j x hi hj => ?_⟩
    have impossible {i j x} (hi : M.PairMember I i x F) (hj : M.PairMember I j x F)
        (hij : M.mem i j) : False := by
      obtain ⟨f, hf', T, ht, hx⟩ := step j x hj
      rcases hx with hx | hx
      · exact ((ht x).mp hx.1).2 ⟨i, (hf'.2 i x).mpr ⟨hij, hi⟩⟩
      · apply hn
        intro y hy
        by_cases hmem : ∃ i, M.PairMember I i y F
        · obtain ⟨i, hi⟩ := hmem
          exact ⟨i, hf.input_mem_of_pairMember hi, hi⟩
        · exact False.elim (hx.1 y ((ht y).mpr ⟨hy, fun ⟨i, hi⟩ => hmem ⟨i, ((hf'.2 i y).mp hi).2⟩⟩))
    rcases hκ.1.wellOrder.linear.compare i (hf.input_mem_of_pairMember hi)
        j (hf.input_mem_of_pairMember hj) with he | hij | hji
    · exact h.1.eq_of_same_members i j he
    · exact False.elim (impossible hi hj hij)
    · exact False.elim (impossible hj hi hji)
  · obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have ht := Structure.IsSequenceOfLength.empty I he
    exact ⟨e, e, ht.1, ⟨ht.2.1, ht.2.2, fun i hi => False.elim (he i hi)⟩,
      fun x hx => False.elim (hn ⟨x, hx⟩)⟩
-- END DONOR Choice.OrdinalEnumeration

end PPAC.Migration.ExistingOrdinalEnumeration
