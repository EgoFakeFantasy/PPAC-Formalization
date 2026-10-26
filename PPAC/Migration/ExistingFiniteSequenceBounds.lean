/- Selected existing YesMetaZFC 7979336 finite-sequence numbering proofs.
Consumer: OpenAI ProbeWords.Raw.cardinal_le, via actual internal Raw codes.
Only imports and enclosing namespaces change; selected proof blocks are locked.
All internal lengths are covered; no object choice or external List recursion. -/
import PPAC.Migration.ExistingCardinalBounds
import YesMetaZFC.SetTheory.FunctionSpaceConstruction
import YesMetaZFC.SetTheory.Ord.FiniteSequenceParsing

namespace PPAC.Migration.ExistingFiniteSequenceBounds
open YesMetaZFC SetTheory SetTheory.ZF SetTheory.Definitional.Project
open ExistingCardinalBounds
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

-- BEGIN DONOR Card.FiniteSequenceSyntax
def Fseq_space_d (ω X S : M.Domain) : Prop :=
  ∀ F, M.mem F S ↔ ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I F n X

def fseq_space_m {d} (ω X S : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest S.weaken) (.existsE (.conj (.mem .newest ω.weaken.weaken)
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest X.weaken.weaken))))
derive_free_closed fseq_space_m

theorem fseq_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X S : Term d) :
    Formula.satisfies ρ (fseq_space_m (𝒞 := 𝒞) ω X S) ↔
      Fseq_space_d I (ω.eval ρ) (X.eval ρ) (S.eval ρ) := by
  simp only [fseq_space_m, Fseq_space_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Fseq_pair_d (Q J L P x z : M.Domain) : Prop :=
  ∃ a b p, M.PairMember I P a L ∧ M.PairMember I x b Q ∧ I.Codes p a b ∧ M.PairMember I p z J

def fseq_pair_m {d} (Q J L P x z : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 P.weaken.weaken.weaken (.bound 2) L.weaken.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 x.weaken.weaken.weaken (.bound 1) Q.weaken.weaken.weaken) (.conj
    (𝒞.code .newest (.bound 2) (.bound 1))
    (Formula.orderedPairMem 𝒞 .newest z.weaken.weaken.weaken J.weaken.weaken.weaken))))))
derive_free_closed fseq_pair_m

theorem fseq_pair_sat_l {d} (ρ : Env M d) (Q J L P x z : Term d) :
    Formula.satisfies ρ (fseq_pair_m (𝒞 := 𝒞) Q J L P x z) ↔
      Fseq_pair_d I (Q.eval ρ) (J.eval ρ) (L.eval ρ) (P.eval ρ) (x.eval ρ) (z.eval ρ) := by
  simp only [fseq_pair_m, Fseq_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Fseq_snoc_d (Q J L m F z : M.Domain) : Prop :=
  ∃ P x, M.IsRestrictionOf I P F m ∧ M.PairMember I m x F ∧ Fseq_pair_d I Q J L P x z

def fseq_snoc_m {d} (Q J L m F z : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (Formula.isRestriction 𝒞 (.bound 1) F.weaken.weaken m.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 m.weaken.weaken .newest F.weaken.weaken)
      (fseq_pair_m (𝒞 := 𝒞) Q.weaken.weaken J.weaken.weaken L.weaken.weaken
        (.bound 1) .newest z.weaken.weaken))))
derive_free_closed fseq_snoc_m

theorem fseq_snoc_sat_l {d} (ρ : Env M d) (Q J L m F z : Term d) :
    Formula.satisfies ρ (fseq_snoc_m (𝒞 := 𝒞) Q J L m F z) ↔
      Fseq_snoc_d I (Q.eval ρ) (J.eval ρ) (L.eval ρ) (m.eval ρ) (F.eval ρ) (z.eval ρ) := by
  simp only [fseq_snoc_m, Fseq_snoc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isRestriction_iff I, Formula.satisfies_orderedPairMem_iff I,
    fseq_pair_sat_l I, Definitional.Term.eval_weaken]
  rfl

def Fseq_at_d (X Q J H F z : M.Domain) : Prop :=
  ∃ n, M.IsDomainOf I n H ∧ M.IsSetFunctionFromTo I F n X ∧
    (((∀ i, ¬ M.mem i n) ∧ ∀ i, ¬ M.mem i z) ∨ ∃ m L,
      M.SuccessorOf n m ∧ M.PairMember I m L H ∧ Fseq_snoc_d I Q J L m F z)

def fseq_at_m {d} (X Q J H F z : Term d) : Formula 1 d :=
  .existsE (.conj (Formula.isDomain 𝒞 .newest H.weaken) (.conj
    (Formula.isFunctionFromTo 𝒞 F.weaken .newest X.weaken) (.disj
    (.conj (Formula.isEmpty .newest) (Formula.isEmpty z.weaken))
    (.existsE (.existsE (.conj (Formula.isSuccessor (.bound 2) (.bound 1)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken)
      (fseq_snoc_m (𝒞 := 𝒞) Q.weaken.weaken.weaken J.weaken.weaken.weaken .newest
        (.bound 1) F.weaken.weaken.weaken z.weaken.weaken.weaken))))))))
derive_free_closed fseq_at_m

theorem fseq_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X Q J H F z : Term d) :
    Formula.satisfies ρ (fseq_at_m (𝒞 := 𝒞) X Q J H F z) ↔
      Fseq_at_d I (X.eval ρ) (Q.eval ρ) (J.eval ρ) (H.eval ρ) (F.eval ρ) (z.eval ρ) := by
  simp only [fseq_at_m, Fseq_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_isDomain_iff I, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I,
    fseq_snoc_sat_l I, Definitional.Term.eval_weaken]
  rfl

def Fseq_step_d (κ X S Q J H K : M.Domain) : Prop :=
  M.IsSetRelation I K ∧ ∀ F z, M.PairMember I F z K ↔
    M.mem F S ∧ M.mem z κ ∧ Fseq_at_d I X Q J H F z

def fseq_step_m {d} (κ X S Q J H K : Term d) : Formula 1 d :=
  .conj (Formula.isRelation 𝒞 K) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest K.weaken.weaken) (.conj
    (.mem (.bound 1) S.weaken.weaken) (.conj (.mem .newest κ.weaken.weaken)
    (fseq_at_m (𝒞 := 𝒞) X.weaken.weaken Q.weaken.weaken J.weaken.weaken H.weaken.weaken (.bound 1) .newest))))))
derive_free_closed fseq_step_m

theorem fseq_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X S Q J H K : Term d) :
    Formula.satisfies ρ (fseq_step_m (𝒞 := 𝒞) κ X S Q J H K) ↔
      Fseq_step_d I (κ.eval ρ) (X.eval ρ) (S.eval ρ) (Q.eval ρ) (J.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [fseq_step_m, Fseq_step_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, fseq_at_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def fseq_env_l (κ X S Q J : M.Domain) : Env M 5 :=
  ⟨Fin.cases J (Fin.cases Q (Fin.cases S (Fin.cases X (fun _ => κ)))), fun _ => κ⟩

def fseq_step_s : BinarySchema 5 where
  body := fseq_step_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

theorem fseq_op_l (hE : Extensional M) (κ X S Q J : M.Domain) :
    (fseq_step_s (𝒞 := 𝒞)).denote (fseq_env_l κ X S Q J) = Fseq_step_d I κ X S Q J := by
  funext H K
  apply propext
  exact fseq_step_sat_l I hE _ _ _ _ _ _ _ _
-- END DONOR Card.FiniteSequenceSyntax

-- BEGIN DONOR Card.FiniteSequenceRecursion
/-- 任意字母表的全部内部有限序列组成实际集合。 -/
theorem fseq_space_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (X : M.Domain) :
    ∃ S, Fseq_space_d I ω X S := by
  obtain ⟨D, hD⟩ := exists_cartesianProduct hZF I ω X
  obtain ⟨U, hU⟩ := exists_powerSet hZF D
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 3))
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest (.bound 2))) }
  have hφ F : φ.denote ρ F ↔ ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I F n X := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1]
    rfl
  obtain ⟨S, hS⟩ := separation_exists_d hZF φ ρ U
  refine ⟨S, fun F => (hS F).trans ?_⟩
  rw [show Formula.satisfies (ρ.push F) φ.body ↔ _ from hφ F]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨n, hn, hF⟩ := h
  apply (hU F).mpr
  intro p hp
  obtain ⟨i, x, hc⟩ := hF.1.1 p hp
  have hi : M.PairMember I i x F := ⟨p, hc, hp⟩
  exact (hD p).mpr ⟨i, hω.transitive hZF n hn i (hF.input_mem_of_pairMember hi),
    x, hF.output_mem_of_pairMember hi, hc⟩

theorem fseq_step_exists_l (hZF : M.Models ZF) (κ X S Q J H : M.Domain) :
    ∃ K, Fseq_step_d I κ X S Q J H K := by
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (modelsKP hZF) S κ
  let ρ := (fseq_env_l κ X S Q J).push H
  let φ : BinarySchema 6 := {
    body := .conj (.mem (.bound 1) (.bound 5)) (.conj (.mem .newest (.bound 7))
      (fseq_at_m (𝒞 := 𝒞) (.bound 6) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)) }
  have hφ F z : φ.denote ρ F z ↔ M.mem F S ∧ M.mem z κ ∧ Fseq_at_d I X Q J H F z := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      fseq_at_sat_l I hZF.1]
    rfl
  obtain ⟨K, hK, hk⟩ := exists_setRelationOn_of_denote hZF I φ ρ U
  refine ⟨K, hK.1, fun F z => (hk F z).trans ?_⟩
  exact ⟨fun h => (hφ F z).mp h.2.2, fun h =>
    ⟨(hU F).mpr (Or.inl h.1), (hU z).mpr (Or.inr h.2.1), (hφ F z).mpr h⟩⟩

/-- 全部编号层统一来自一条实际 ω 递归，尚不预设编号性质。 -/
theorem fseq_recursion_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (κ X S Q J : M.Domain) :
    ∃ H, M.IsRecursiveSequence I (Fseq_step_d I κ X S Q J) H ω := by
  have ho := fseq_op_l I hZF.1 κ X S Q J
  have hc : M.IsClassFunctionOnTransfiniteSequences I ((fseq_step_s (𝒞 := 𝒞)).denote (fseq_env_l κ X S Q J)) := by
    rw [ho]
    intro P _
    obtain ⟨K, hK⟩ := fseq_step_exists_l I hZF κ X S Q J P
    exact ⟨K, hK, fun L hL => hL.1.eq_of_pairMember_iff hZF.1 hK.1
      (fun F z => (hL.2 F z).trans (hK.2 F z).symm)⟩
  obtain ⟨H, hH⟩ := recursiveSequence_exists hZF I (fseq_env_l κ X S Q J) (fseq_step_s (𝒞 := 𝒞)) hc (hω.isOrdinal hZF)
  exact ⟨H, by simpa only [ho] using hH⟩


theorem fseq_at_zero_l (hE : Extensional M) {X Q J H n} (hd : M.IsDomainOf I n H)
    (hn : ∀ i, ¬ M.mem i n) (F z : M.Domain) :
    Fseq_at_d I X Q J H F z ↔ M.IsSetFunctionFromTo I F n X ∧ ∀ i, ¬ M.mem i z := by
  constructor
  · rintro ⟨m, hm, hF, he | ⟨i, L, hi, _⟩⟩
    · have hh := hm.eq hE hd
      subst m
      exact ⟨hF, he.2⟩
    · have hh := hm.eq hE hd
      subst m
      exact (hn i hi.predecessor_mem).elim
  · exact fun ⟨hF, hz⟩ => ⟨n, hd, hF, Or.inl ⟨hn, hz⟩⟩

theorem fseq_at_succ_l (hE : Extensional M) {X Q J H n m L}
    (hd : M.IsDomainOf I n H) (hH : M.IsSetFunction I H) (hm : M.IsOrdinal m)
    (hn : M.SuccessorOf n m) (hL : M.PairMember I m L H) (F z : M.Domain) :
    Fseq_at_d I X Q J H F z ↔ M.IsSetFunctionFromTo I F n X ∧ Fseq_snoc_d I Q J L m F z := by
  constructor
  · rintro ⟨s, hs, hF, he | ⟨i, K, hi, hK, hz⟩⟩
    · have hh := hs.eq hE hd
      subst s
      exact (he.1 m hn.predecessor_mem).elim
    · have hh := hs.eq hE hd
      subst s
      have hh := hn.predecessor_eq hE hm hi
      subst i
      have hh := hH.2 m K L hK hL
      subst K
      exact ⟨hF, hz⟩
  · exact fun ⟨hF, hz⟩ => ⟨n, hd, hF, Or.inr ⟨m, L, hn, hL, hz⟩⟩
-- END DONOR Card.FiniteSequenceRecursion

-- BEGIN DONOR Card.FiniteSequenceNumbering
theorem fseq_snoc_unique_l (hE : Extensional M) {Q J L m F z w}
    (hQ : M.IsSetFunction I Q) (hJ : M.IsSetFunction I J) (hL : M.IsSetFunction I L)
    (hF : M.IsSetFunction I F) (hz : Fseq_snoc_d I Q J L m F z) (hw : Fseq_snoc_d I Q J L m F w) : z = w := by
  obtain ⟨P, x, hP, hx, a, b, p, ha, hb, hp, hz⟩ := hz
  obtain ⟨T, y, hT, hy, c, d, q, hc, hd, hq, hw⟩ := hw
  have he := hP.eq hE hT
  subst T
  have he := hF.2 m x y hx hy
  subst y
  have he := hL.2 P a c ha hc
  subst c
  have he := hQ.2 x b d hb hd
  subst d
  have he := I.unique hp hq
  subst q
  exact hJ.2 p z w hz hw

theorem fseq_snoc_injective_l (hE : Extensional M) {Q J L A X W κ m n F G z}
    (hQ : M.IsSetInjectionFromTo I Q X κ) (hJ : M.IsSetInjectionFromTo I J W κ)
    (hL : M.IsSetInjectionFromTo I L A κ) (hn : M.IsOrdinal n) (hs : M.SuccessorOf n m)
    (hF : M.IsSetFunctionFromTo I F n X) (hG : M.IsSetFunctionFromTo I G n X)
    (hz : Fseq_snoc_d I Q J L m F z) (hw : Fseq_snoc_d I Q J L m G z) : F = G := by
  obtain ⟨P, x, hP, hx, a, b, p, ha, hb, hp, hz⟩ := hz
  obtain ⟨T, y, hT, hy, c, d, q, hc, hd, hq, hw⟩ := hw
  have he := hJ.2 p q z hz hw
  subst q
  obtain ⟨he, hf⟩ := I.injective hp hq
  subst c
  subst d
  have hx' := hQ.2 x y b hb hd
  subst y
  exact Structure.IsSequenceOfLength.eq_of_restriction_eq_of_last hE
    ⟨hn, hF.1, hF.2.1⟩ ⟨hn, hG.1, hG.2.1⟩ hs hs hP hT (hL.2 P T a ha hc) hx hy


theorem fseq_snoc_total_l (hZF : M.Models ZF) {κ X W Q J L A m n F}
    (hW : M.IsCartesianProduct I W κ κ) (hQ : M.IsSetFunctionFromTo I Q X κ)
    (hJ : M.IsSetFunctionFromTo I J W κ) (hA : M.IsFunctionSpace I A m X)
    (hL : M.IsSetFunctionFromTo I L A κ) (hs : M.SuccessorOf n m) (hF : M.IsSetFunctionFromTo I F n X) :
    ∃ z, M.mem z κ ∧ Fseq_snoc_d I Q J L m F z := by
  obtain ⟨P, hP⟩ := exists_restriction hZF I F m
  have hm : M.MemberSubset m n := fun i hi => (hs i).mpr (Or.inl hi)
  obtain ⟨a, ha, hPa⟩ := hL.2.2 P ((hA P).mpr (hP.isSetFunctionFromTo hF hm))
  obtain ⟨x, hx, hFx⟩ := hF.2.2 m hs.predecessor_mem
  obtain ⟨b, hb, hxb⟩ := hQ.2.2 x hx
  obtain ⟨p, hp⟩ := I.total a b
  obtain ⟨z, hz, hpz⟩ := hJ.2.2 p ((hW p).mpr ⟨a, ha, b, hb, hp⟩)
  exact ⟨z, hz, P, x, hP, hFx, a, b, p, hPa, hxb, hp, hpz⟩

/-- 同一内部递归表在每个内部自然数层都给出实际单射 X^n → κ。 -/
theorem fseq_numbering_l (hZF : M.Models ZF) {ω κ X S W Q J H}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ) (hS : Fseq_space_d I ω X S) (hW : M.IsCartesianProduct I W κ κ)
    (hQ : M.IsSetInjectionFromTo I Q X κ) (hJ : M.IsSetInjectionFromTo I J W κ)
    (hH : M.IsRecursiveSequence I (Fseq_step_d I κ X S Q J) H ω) :
    ∀ n, M.mem n ω → ∀ K, M.PairMember I n K H →
      ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A κ := by
  let ρ : Env M 3 := ((⟨fun _ => H, fun _ => H⟩ : Env M 1).push X).push κ
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.existsE
      (.conj (Formula.isFunctionSpace 𝒞 .newest (.bound 2) (.bound 4))
        (Formula.isInjectionFromTo 𝒞 (.bound 1) .newest (.bound 3)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, Formula.isFunctionSpace] }
  have hφ n : φ.denote ρ n ↔ ∀ K, M.PairMember I n K H →
      ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A κ := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isFunctionSpace_iff I hZF.1, Formula.satisfies_isInjectionFromTo_iff I hZF.1]
    rfl
  apply hω.induction (fun n => ∀ K, M.PairMember I n K H →
    ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A κ)
  · obtain ⟨D, hD⟩ := separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro n hn K hK
    -- 零层只有空函数，统一编号为内部零。
    have hnω := (hH.1.2.2 n).mpr ⟨K, hK⟩
    obtain ⟨P, hP, hStep⟩ := hH.2 n hnω K hK
    have hd := (hH.restriction hnω hP).1.2.2
    have he F z : M.PairMember I F z K ↔ M.mem F S ∧ M.mem z κ ∧
        M.IsSetFunctionFromTo I F n X ∧ ∀ i, ¬ M.mem i z :=
      (hStep.2 F z).trans (and_congr_right fun _ => and_congr_right fun _ => fseq_at_zero_l I hZF.1 hd hn F z)
    obtain ⟨A, hA⟩ := exists_functionSpace hZF I n X
    have total F (hF : M.mem F A) : ∃ z, M.mem z κ ∧ M.PairMember I F z K :=
      ⟨n, hωκ n hnω, (he F n).mpr ⟨(hS F).mpr ⟨n, hnω, (hA F).mp hF⟩, hωκ n hnω, (hA F).mp hF, hn⟩⟩
    refine ⟨A, hA, ⟨⟨hStep.1, ?_⟩, ?_, total⟩, ?_⟩
    · intro F z w hz hw
      exact hZF.1.eq_of_same_members z w (fun i => iff_of_false (((he F z).mp hz).2.2.2 i) (((he F w).mp hw).2.2.2 i))
    · intro F
      exact ⟨fun h => (total F h).elim fun z hz => ⟨z, hz.2⟩,
        fun ⟨z, hz⟩ => (hA F).mpr ((he F z).mp hz).2.2.1⟩
    · intro F G z hz hw
      have hf := ((he F z).mp hz).2.2.1
      have hg := ((he G z).mp hw).2.2.1
      exact hf.1.1.eq_of_pairMember_iff hZF.1 hg.1.1 (fun i x =>
        iff_of_false (fun h => hn i (hf.input_mem_of_pairMember h)) (fun h => hn i (hg.input_mem_of_pairMember h)))
  · intro m hm ih n hn K hK
    -- 后继层先限制到 m，再用固定的 J 合并前缀与末项编号。
    have hnω := (hH.1.2.2 n).mpr ⟨K, hK⟩
    obtain ⟨P, hP, hStep⟩ := hH.2 n hnω K hK
    have hd := (hH.restriction hnω hP).1.2.2
    obtain ⟨L, hL⟩ := (hH.1.2.2 m).mp hm
    obtain ⟨A, hA, hInj⟩ := ih L hL
    have hLP := (hP.2 m L).mpr ⟨hn.predecessor_mem, hL⟩
    have he F z : M.PairMember I F z K ↔ M.mem F S ∧ M.mem z κ ∧
        M.IsSetFunctionFromTo I F n X ∧ Fseq_snoc_d I Q J L m F z :=
      (hStep.2 F z).trans (and_congr_right fun _ => and_congr_right fun _ =>
        fseq_at_succ_l I hZF.1 hd (hP.isSetFunction hH.1.2.1) (hω.members_areOrdinals hZF m hm) hn hLP F z)
    obtain ⟨B, hB⟩ := exists_functionSpace hZF I n X
    have total F (hF : M.mem F B) : ∃ z, M.mem z κ ∧ M.PairMember I F z K := by
      obtain ⟨z, hz, hf⟩ := fseq_snoc_total_l I hZF hW hQ.1 hJ.1 hA hInj.1 hn ((hB F).mp hF)
      exact ⟨z, hz, (he F z).mpr ⟨(hS F).mpr ⟨n, hnω, (hB F).mp hF⟩, hz, (hB F).mp hF, hf⟩⟩
    refine ⟨B, hB, ⟨⟨hStep.1, ?_⟩, ?_, total⟩, ?_⟩
    · intro F z w hz hw
      have hf := (he F z).mp hz
      exact fseq_snoc_unique_l I hZF.1 hQ.1.1 hJ.1.1 hInj.1.1 hf.2.2.1.1 hf.2.2.2 ((he F w).mp hw).2.2.2
    · intro F
      exact ⟨fun h => (total F h).elim fun z hz => ⟨z, hz.2⟩,
        fun ⟨z, hz⟩ => (hB F).mpr ((he F z).mp hz).2.2.1⟩
    · intro F G z hz hw
      have hf := (he F z).mp hz
      have hg := (he G z).mp hw
      exact fseq_snoc_injective_l I hZF.1 hQ hJ hInj (hω.members_areOrdinals hZF n hnω) hn
        hf.2.2.1 hg.2.2.1 hf.2.2.2 hg.2.2.2
-- END DONOR Card.FiniteSequenceNumbering

-- BEGIN DONOR Card.FiniteSequenceCountable
/-- κ 小字母表的全部内部有限序列仍为 κ 小；包括非标准有限长度。 -/
theorem fseq_bound_l (hZF : M.Models ZF) {ω κ X S} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hX : M.CardinalLessOrEqual I X κ) (hS : Fseq_space_d I ω X S) : M.CardinalLessOrEqual I S κ := by
  have hωκ := hω.subset_limitOrdinal hZF
    (infiniteCardinal_isLimitOrdinal hZF I hω (omega_cardinal_l I hZF hω) hκ)
  obtain ⟨Q, hQ⟩ := hX
  obtain ⟨W, hW⟩ := exists_cartesianProduct hZF I κ κ
  obtain ⟨T, hT⟩ := exists_identityBijection hZF I κ
  obtain ⟨J, hJ⟩ := infinite_product_l I hZF hω hκ ⟨T, hT.1⟩ ⟨T, hT.1⟩ hW
  obtain ⟨H, hH⟩ := fseq_recursion_l I hZF hω κ X S Q J
  have levels := fseq_numbering_l I hZF hω hωκ hS hW hQ hJ hH
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push H).push J
  let φ : BinarySchema 4 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 3) (.bound 9)) (.conj
      (Formula.isFunctionFromTo 𝒞 (.bound 5) (.bound 3) (.bound 8)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 2) (.bound 7)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 1) (.bound 2)) (.conj
      (𝒞.code .newest (.bound 3) (.bound 1))
      (Formula.orderedPairMem 𝒞 .newest (.bound 4) (.bound 6)))))))))) }
  have hφ F z : φ.denote ρ F z ↔ ∃ n K t p,
      M.mem n ω ∧ M.IsSetFunctionFromTo I F n X ∧ M.PairMember I n K H ∧
        M.PairMember I F t K ∧ I.Codes p n t ∧ M.PairMember I p z J := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro F hF
    obtain ⟨n, hn, hf⟩ := (hS F).mp hF
    obtain ⟨K, hK⟩ := (hH.1.2.2 n).mp hn
    obtain ⟨A, hA, hk⟩ := levels n hn K hK
    obtain ⟨t, ht, hFt⟩ := hk.1.2.2 F ((hA F).mpr hf)
    obtain ⟨p, hp⟩ := I.total n t
    obtain ⟨z, _, hz⟩ := hJ.1.2.2 p ((hW p).mpr ⟨n, hωκ n hn, t, ht, hp⟩)
    exact ⟨z, (hφ F z).mpr ⟨n, K, t, p, hn, hf, hK, hFt, hp, hz⟩⟩
  · intro F _ z w hz hw
    obtain ⟨n, K, t, p, hn, hf, hK, hFt, hp, hz⟩ := (hφ F z).mp hz
    obtain ⟨m, L, s, q, _, hg, hL, hFs, hq, hw⟩ := (hφ F w).mp hw
    have he := hf.2.1.eq hZF.1 hg.2.1
    subst m
    have he := hH.1.2.1.2 n K L hK hL
    subst L
    obtain ⟨A, _, hk⟩ := levels n hn K hK
    have he := hk.1.1.2 F t s hFt hFs
    subst s
    have he := I.unique hp hq
    subst q
    exact hJ.1.1.2 p z w hz hw
  · intro F z _ hz
    obtain ⟨_, _, _, _, _, _, _, _, _, hz⟩ := (hφ F z).mp hz
    exact hJ.1.output_mem_of_pairMember hz
  · intro F G z _ _ hz hw
    obtain ⟨n, K, t, p, hn, _, hK, hFt, hp, hz⟩ := (hφ F z).mp hz
    obtain ⟨m, L, s, q, _, _, hL, hGs, hq, hw⟩ := (hφ G z).mp hw
    have he := hJ.2 p q z hz hw
    subst q
    obtain ⟨he, hf⟩ := I.injective hp hq
    subst m
    subst s
    have he := hH.1.2.1.2 n K L hK hL
    subst L
    obtain ⟨A, _, hk⟩ := levels n hn K hK
    exact hk.2 F G t hFt hGs
-- END DONOR Card.FiniteSequenceCountable

end PPAC.Migration.ExistingFiniteSequenceBounds
