/- Exact existing finite-address methods needed by pinned
AssignedGraphs.CountableHull.exists_closed:296-324 (full omega-branching terms).
Retain the donor finite parsing/cons/prefix/child proofs; the carrier itself
is the already migrated ExistingFiniteSequenceBounds.Fseq_space_d. -/
import PPAC.Migration.ExistingFiniteSequenceBounds

namespace PPAC.Migration.ExistingTreeAddresses
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingFiniteSequenceBounds
open YesMetaZFC.SetTheory.ZF (modelsKP)
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

-- Retained producer: Card/FiniteSequenceEnd.lean
def Fseq_end_d (ω F f p : M.Domain) : Prop := ∃ n m,
  M.IsFiniteSequenceLastDecomposition I ω F n m f p

def fseq_end_m {d} (ω F f p : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) ω.weaken.weaken) (.conj
    (Formula.isSequenceOfLength 𝒞 F.weaken.weaken (.bound 1)) (.conj
    (.mem .newest ω.weaken.weaken) (.conj (Formula.isSuccessor (.bound 1) .newest) (.conj
    (Formula.isSequenceOfLength 𝒞 f.weaken.weaken .newest) (.conj
    (Formula.isRestriction 𝒞 f.weaken.weaken F.weaken.weaken .newest)
    (Formula.orderedPairMem 𝒞 .newest p.weaken.weaken F.weaken.weaken))))))))
derive_free_closed fseq_end_m

theorem fseq_end_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F f p : Term d) :
    Formula.satisfies ρ (fseq_end_m (𝒞 := 𝒞) ω F f p) ↔
      Fseq_end_d I (ω.eval ρ) (F.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [fseq_end_m, Fseq_end_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSequenceOfLength_iff I hE,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  apply exists_congr
  intro n
  apply exists_congr
  intro m
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1,
      ⟨h.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h => ⟨h.source.1, h.source.2, h.predecessor_mem_omega, h.length_successor,
      h.prefix_sequence.2, h.prefix_restriction, h.last_value⟩⟩

theorem fseq_end_unique_l (hE : Extensional M) {ω F f p g q}
    (h : Fseq_end_d I ω F f p) (k : Fseq_end_d I ω F g q) : f = g ∧ p = q := by
  obtain ⟨n, m, h⟩ := h
  obtain ⟨n', m', k⟩ := k
  have he := h.source.length_unique hE k.source
  subst n'
  exact (h.components_unique hE k).2

/-- 相同前缀和末项决定唯一的内部有限列；长度也从前缀图中恢复。 -/
theorem fseq_end_rebuild_l (hE : Extensional M) {ω F G f p}
    (h : Fseq_end_d I ω F f p) (k : Fseq_end_d I ω G f p) : F = G := by
  obtain ⟨n, m, h⟩ := h
  obtain ⟨n', m', k⟩ := k
  have hm := h.prefix_sequence.length_unique hE k.prefix_sequence
  subst m'
  have hn := hE.eq_of_same_members n n' (fun x => (h.length_successor x).trans (k.length_successor x).symm)
  subst n'
  exact h.sequence_unique_of_components hE k

/-- 将一项追加到内部有限参数列；新增图仍取值于同一集合。 -/
theorem fseq_end_exists_l (hZF : M.Models ZF) {ω n f X p} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hf : M.IsSetFunctionFromTo I f n X) (hp : M.mem p X) :
    ∃ m F, M.mem m ω ∧ M.IsSetFunctionFromTo I F m X ∧ Fseq_end_d I ω F f p := by
  obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
  obtain ⟨F, hF, hFf⟩ := Structure.IsSequenceOfLength.exists_append (value := p)
    (modelsKP hZF) I ⟨(hω.isOrdinal hZF).mem hn, hf.1, hf.2.1⟩ ((hω.isOrdinal hZF).mem hmω) hm
  have hr : M.IsRestrictionOf I f F n := by
    refine ⟨hf.1.1, fun i x => ?_⟩
    constructor
    · exact fun hi => ⟨hf.input_mem_of_pairMember hi, (hFf i x).mpr (Or.inl hi)⟩
    · rintro ⟨hi, hx⟩
      rcases (hFf i x).mp hx with hx | ⟨rfl, _⟩
      · exact hx
      · exact ((hω.isOrdinal hZF).mem hn).wellOrder.linear.irrefl _ hi hi |>.elim
  refine ⟨m, F, hmω, ⟨hF.2.1, hF.2.2, fun i hi => ?_⟩, m, n,
    ⟨⟨hmω, hF⟩, hn, hm, ⟨hn, (hω.isOrdinal hZF).mem hn, hf.1, hf.2.1⟩, hr,
      (hFf n p).mpr (Or.inr ⟨rfl, rfl⟩)⟩⟩
  obtain ⟨x, hx⟩ := (hF.2.2 i).mp hi
  refine ⟨x, ?_, hx⟩
  exact ((hFf i x).mp hx).elim hf.output_mem_of_pairMember (fun h => h.2.symm ▸ hp)

-- Retained producer: Descriptive/Prefix.lean
theorem ds_restrict_iff_l {s f n X : M.Domain} (hs : M.IsSetFunctionFromTo I s n X)
    (hf : M.IsSetFunction I f) : M.IsRestrictionOf I s f n ↔ M.MemberSubset s f := by
  constructor
  · intro h p hp
    obtain ⟨i, x, hc⟩ := hs.1.1 p hp
    obtain ⟨q, hq, hqf⟩ := ((h.2 i x).mp ⟨p, hc, hp⟩).2
    exact (I.unique hc hq).symm ▸ hqf
  · intro h
    refine ⟨hs.1.1, fun i x => ⟨fun hx => ?_, fun ⟨hi, hx⟩ => ?_⟩⟩
    · exact ⟨hs.input_mem_of_pairMember hx, hx.elim fun p hp => ⟨p, hp.1, h p hp.2⟩⟩
    · obtain ⟨y, _, hy⟩ := hs.2.2 i hi
      have hyf : M.PairMember I i y f := hy.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
      exact hf.2 i y x hyf hx ▸ hy

-- Retained producer: Descriptive/Path.lean
def Step_d (ω s t : M.Domain) : Prop := ∃ a, Fseq_end_d I ω t s a
def step_m {d} (ω s t : Term d) : Formula 1 d :=
  .existsE (fseq_end_m (𝒞 := 𝒞) ω.weaken t.weaken s.weaken .newest)
derive_free_closed step_m

theorem step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω s t : Term d) :
    Formula.satisfies ρ (step_m (𝒞 := 𝒞) ω s t) ↔ Step_d I (ω.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [step_m, Step_d, Formula.satisfies_exists_iff, fseq_end_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem ds_empty_fun_l {e X : M.Domain} (he : ∀ x, ¬ M.mem x e) : M.IsSetFunctionFromTo I e e X :=
  ⟨⟨fun p hp => (he p hp).elim, fun _ _ _ h => (h.elim fun p hp => he p hp.2).elim⟩,
    fun i => ⟨fun hi => (he i hi).elim, fun ⟨_, p, _, hp⟩ => (he p hp).elim⟩,
    fun i hi => (he i hi).elim⟩

-- Retained producer: Descriptive/TreeCons.lean
def Cons_d (z a s t : M.Domain) : Prop := M.IsSetRelation I t ∧ ∀ j x,
  M.PairMember I j x t ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x s ∧ M.SuccessorOf j i
def cons_m {d} (z a s t : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 t)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest t.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) z.weaken.weaken) (Formula.extensionalEq .newest a.weaken.weaken))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) s.weaken.weaken.weaken)
        (Formula.isSuccessor (.bound 2) .newest)))))))
derive_free_closed cons_m
theorem cons_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z a s t : Term d) :
    Formula.satisfies ρ (cons_m (𝒞 := 𝒞) z a s t) ↔
      Cons_d I (z.eval ρ) (a.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [cons_m, Cons_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

omit I in
theorem tree_successor_le_l (hZF : M.Models ZF) {ω n i j : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hi : M.mem i n) (hj : M.SuccessorOf j i) : j = n ∨ M.mem j n := by
  obtain ⟨j', hj', hjω⟩ := hω.1.2 i (hω.transitive hZF n hn i hi)
  have e := Structure.SuccessorOf.eq hZF.1 hj' hj
  have hjω := e ▸ hjω
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare j hjω n hn with e | h | h
  · exact Or.inl (hZF.1.eq_of_same_members j n e)
  · exact Or.inr h
  · rcases (hj n).mp h with h | e
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (((hω.isOrdinal hZF).mem hn).transitive i hi n h)).elim
    · have e := hZF.1.eq_of_same_members n i e
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (e.symm ▸ hi)).elim

theorem cons_unique_l (hE : Extensional M) {z a s t u : M.Domain} (h : Cons_d I z a s t)
    (k : Cons_d I z a s u) : t = u := h.1.eq_of_pairMember_iff hE k.1 (fun j x => (h.2 j x).trans (k.2 j x).symm)

/-- 首项拼接生成后继长度的实际函数图。 -/
theorem cons_exists_l (hZF : M.Models ZF) {ω z a s n} (hω : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a ω) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n ω) :
    ∃ k t, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k ω ∧ Cons_d I z a s t := by
  obtain ⟨k, hk, hkω⟩ := hω.1.2 n hn
  have hzK := Structure.IsOrdinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
    ((hω.isOrdinal hZF).mem hkω) ⟨n, hk.predecessor_mem⟩ hz
  let ρ : Env M 3 := ((⟨fun _ => s, fun _ => s⟩ : Env M 1).push a).push z
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5))
        (Formula.isSuccessor (.bound 2) .newest))) }
  have hp j x : φ.denote ρ j x ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x s ∧ M.SuccessorOf j i := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff]; rfl
  obtain ⟨t, ht, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := ω)
    (by
      intro j hj
      classical
      by_cases h0 : ∀ x, ¬ M.mem x j
      · exact ⟨a, (hp j a).mpr (Or.inl ⟨hZF.1.eq_of_same_members j z (fun x => iff_of_false (h0 x) (hz x)), rfl⟩)⟩
      · have hne : ∃ x, M.mem x j := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
        obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive hZF k hkω j hj) hne
        have hiK := ((hω.isOrdinal hZF).mem hkω).transitive j hj i hji.predecessor_mem
        have hi : M.mem i n := ((hk i).mp hiK).elim id (fun e => by
          have ei := hZF.1.eq_of_same_members i n e
          have ej := Structure.SuccessorOf.eq hZF.1 (ei ▸ hji) hk
          exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (ej ▸ hj)).elim)
        obtain ⟨x, _, hx⟩ := hs.2.2 i hi
        exact ⟨x, (hp j x).mpr (Or.inr ⟨i, hx, hji⟩)⟩)
    (by
      intro j _ x y hx hy
      rcases (hp j x).mp hx with ⟨e, rfl⟩ | ⟨i, hi, hji⟩ <;>
        rcases (hp j y).mp hy with ⟨e', rfl⟩ | ⟨i', hi', hji'⟩
      · rfl
      · exact (hz i' (e ▸ hji'.predecessor_mem)).elim
      · exact (hz i (e' ▸ hji.predecessor_mem)).elim
      · have e := Structure.SuccessorOf.predecessor_eq hZF.1
          (((hω.isOrdinal hZF).mem hn).mem (hs.input_mem_of_pairMember hi)) hji hji'
        exact hs.1.2 i x y hi (e.symm ▸ hi'))
    (fun j x _ hx => ((hp j x).mp hx).elim (fun h => h.2.symm ▸ ha)
      (fun ⟨_, hi, _⟩ => hs.output_mem_of_pairMember hi))
  refine ⟨k, t, hkω, hk, ht, ht.1.1, fun j x => (he j x).trans ?_⟩
  rw [hp j x]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨e, _⟩ | ⟨i, hi, hji⟩
  · exact e.symm ▸ hzK
  · exact (tree_successor_le_l hZF hω hn (hs.input_mem_of_pairMember hi) hji).elim
      (fun e => e.symm ▸ hk.predecessor_mem) (fun h => (hk j).mpr (Or.inl h))

/-- 拼接的图包含恰好对应首项相同和尾列包含。 -/
theorem cons_subset_l (hZF : M.Models ZF) {ω z a b s t u v n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n ω)
    (hu : Cons_d I z a s u) (hv : Cons_d I z b t v) :
    M.MemberSubset u v ↔ a = b ∧ M.MemberSubset s t := by
  have lift {P Q i x} (h : M.MemberSubset P Q) (hp : M.PairMember I i x P) : M.PairMember I i x Q :=
    hp.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
  constructor
  · intro h
    have hab : a = b := ((hv.2 z a).mp (lift h ((hu.2 z a).mpr (Or.inl ⟨rfl, rfl⟩)))).elim And.right
      (fun ⟨i, _, hi⟩ => (hz i hi.predecessor_mem).elim)
    refine ⟨hab, fun p hp => ?_⟩
    obtain ⟨i, x, hpx⟩ := hs.1.1 p hp
    have hi := hs.input_mem_of_pairMember ⟨p, hpx, hp⟩
    obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive hZF n hn i hi)
    have hx := (hv.2 j x).mp (lift h ((hu.2 j x).mpr (Or.inr ⟨i, ⟨p, hpx, hp⟩, hj⟩)))
    have hxt : M.PairMember I i x t := by
      rcases hx with ⟨e, _⟩ | ⟨i', hx, hj'⟩
      · exact (hz i (e ▸ hj.predecessor_mem)).elim
      · have e := Structure.SuccessorOf.predecessor_eq hZF.1 (((hω.isOrdinal hZF).mem hn).mem hi) hj hj'
        exact e.symm ▸ hx
    obtain ⟨q, hq, hqt⟩ := hxt
    exact (I.unique hpx hq).symm ▸ hqt
  · rintro ⟨rfl, hst⟩ p hp
    obtain ⟨j, x, hc⟩ := hu.1 p hp
    have hx := (hu.2 j x).mp ⟨p, hc, hp⟩
    have hxt : M.PairMember I j x v := (hv.2 j x).mpr (hx.imp_right
      (fun ⟨i, hi, hij⟩ => ⟨i, lift hst hi, hij⟩))
    obtain ⟨q, hq, hqv⟩ := hxt
    exact (I.unique hc hq).symm ▸ hqv

theorem cons_type_l (hZF : M.Models ZF) {ω z a s t n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a ω) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (ht : Cons_d I z a s t) :
    ∃ k, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k ω := by
  obtain ⟨k, u, hk, hkn, hu, hc⟩ := cons_exists_l I hZF hω hz ha hn hs
  exact ⟨k, hk, hkn, cons_unique_l I hZF.1 hc ht ▸ hu⟩

theorem cons_injective_l (hZF : M.Models ZF) {ω z a b s t v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hm : M.mem m ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (ht : M.IsSetFunctionFromTo I t m ω)
    (hu : Cons_d I z a s v) (hv : Cons_d I z b t v) : a = b ∧ s = t := by
  have h := (cons_subset_l I hZF hω hz hn hs hu hv).mp (fun _ => id)
  have k := (cons_subset_l I hZF hω hz hm ht hv hu).mp (fun _ => id)
  exact ⟨h.1, hZF.1.eq_of_same_members s t (fun p => ⟨h.2 p, k.2 p⟩)⟩

/-- 直接子边等价于图包含与长度相差一个后继。 -/
theorem tree_step_iff_l (hZF : M.Models ZF) {ω s t n m} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n ω)
    (ht : M.IsSetFunctionFromTo I t m ω) :
    Step_d I ω s t ↔ M.SuccessorOf m n ∧ M.MemberSubset s t := by
  constructor
  · rintro ⟨a, j, k, h⟩
    have e := h.source.2.2.2.eq hZF.1 ht.2.1
    subst j
    have e := h.prefix_sequence.2.2.2.eq hZF.1 hs.2.1
    subst k
    exact ⟨h.length_successor, (ds_restrict_iff_l I hs ht.1).mp h.prefix_restriction⟩
  · rintro ⟨h, hst⟩
    obtain ⟨a, _, ha⟩ := ht.2.2 n h.predecessor_mem
    exact ⟨a, m, n, ⟨⟨hm, (hω.isOrdinal hZF).mem hm, ht.1, ht.2.1⟩, hn, h,
      ⟨hn, (hω.isOrdinal hZF).mem hn, hs.1, hs.2.1⟩,
      (ds_restrict_iff_l I hs ht.1).mpr hst, ha⟩⟩

theorem cons_step_l (hZF : M.Models ZF) {ω z a b s t u v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a ω) (hb : M.mem b ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n ω)
    (ht : M.IsSetFunctionFromTo I t m ω) (hu : Cons_d I z a s u) (hv : Cons_d I z b t v) :
    Step_d I ω u v ↔ a = b ∧ Step_d I ω s t := by
  obtain ⟨j, hj, hjn, huf⟩ := cons_type_l I hZF hω hz ha hn hs hu
  obtain ⟨k, hk, hkm, hvf⟩ := cons_type_l I hZF hω hz hb hm ht hv
  rw [tree_step_iff_l I hZF hω hj hk huf hvf, cons_subset_l I hZF hω hz hn hs hu hv,
    tree_step_iff_l I hZF hω hn hm hs ht]
  constructor
  · rintro ⟨hkj, hab, hst⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem hm) hkm hkj
    exact ⟨hab, e.symm ▸ hjn, hst⟩
  · rintro ⟨hab, hmn, hst⟩
    have e := Structure.SuccessorOf.eq hZF.1 hmn hjn
    exact ⟨e ▸ hkm, hab, hst⟩

-- Retained producer: Descriptive/TreeTail.lean
theorem tree_empty_domain_l (hE : Extensional M) {z t X} (hz : ∀ x, ¬ M.mem x z)
    (ht : M.IsSetFunctionFromTo I t z X) : t = z := by
  apply hE.eq_of_same_members
  intro p
  exact iff_of_false (fun hp => (ht.1.1 p hp).elim fun i ⟨x, hc⟩ =>
    hz i (ht.input_mem_of_pairMember ⟨p, hc, hp⟩)) (hz p)

/-- 空列或唯一的首项加尾列；尾列仍属于同一内部有限列空间。 -/
theorem cons_cases_l (hZF : M.Models ZF) {ω A z t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) (ht : M.mem t A) :
    t = z ∨ ∃ a s, M.mem a ω ∧ M.mem s A ∧ Cons_d I z a s t := by
  classical
  obtain ⟨n, hn, ht⟩ := (hA t).mp ht
  by_cases h0 : ∀ x, ¬ M.mem x n
  · have en := hZF.1.eq_of_same_members n z (fun x => iff_of_false (h0 x) (hz x))
    exact Or.inl (tree_empty_domain_l I hZF.1 hz (en ▸ ht))
  have hne : ∃ x, M.mem x n := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
  obtain ⟨m, hm, hnm⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn hne
  obtain ⟨a, ha, hza⟩ := ht.2.2 z (Structure.IsOrdinal.empty_mem_of_nonempty
    (ZF.modelsKP hZF) ((hω.isOrdinal hZF).mem hn) hne hz)
  let ρ : Env M 1 := ⟨fun _ => t, fun _ => t⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (Formula.isSuccessor .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have hp i x : φ.denote ρ i x ↔ ∃ j, M.SuccessorOf j i ∧ M.PairMember I j x t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨s, hs, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := ω)
    (by
      intro i hi
      obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive hZF m hm i hi)
      have hjn : M.mem j n := (tree_successor_le_l hZF hω hm hi hj).elim
        (fun e => e.symm ▸ hnm.predecessor_mem) (fun h => (hnm j).mpr (Or.inl h))
      obtain ⟨x, _, hx⟩ := ht.2.2 j hjn
      exact ⟨x, (hp i x).mpr ⟨j, hj, hx⟩⟩)
    (by
      intro i _ x y hx hy
      obtain ⟨j, hj, hx⟩ := (hp i x).mp hx
      obtain ⟨k, hk, hy⟩ := (hp i y).mp hy
      exact ht.1.2 j x y hx (Structure.SuccessorOf.eq hZF.1 hk hj ▸ hy))
    (fun i x _ hx => ((hp i x).mp hx).elim fun _ h => ht.output_mem_of_pairMember h.2)
  refine Or.inr ⟨a, s, ha, (hA s).mpr ⟨m, hm, hs⟩, ht.1.1, fun j x => ⟨?_, ?_⟩⟩
  · intro hx
    by_cases h0 : ∀ i, ¬ M.mem i j
    · have e := hZF.1.eq_of_same_members j z (fun i => iff_of_false (h0 i) (hz i))
      exact Or.inl ⟨e, ht.1.2 j x a hx (e.symm ▸ hza)⟩
    · have hne : ∃ i, M.mem i j := Classical.byContradiction (fun h => h0 (fun i hi => h ⟨i, hi⟩))
      have hj := ht.input_mem_of_pairMember hx
      obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive hZF n hn j hj) hne
      have hin := ((hω.isOrdinal hZF).mem hn).transitive j hj i hji.predecessor_mem
      have hi : M.mem i m := ((hnm i).mp hin).elim id (fun e => by
        have ei := hZF.1.eq_of_same_members i m e
        have ej := Structure.SuccessorOf.eq hZF.1 (ei ▸ hji) hnm
        exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (ej ▸ hj)).elim)
      exact Or.inr ⟨i, (he i x).mpr ⟨hi, (hp i x).mpr ⟨j, hji, hx⟩⟩, hji⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hj⟩)
    · exact hza
    · obtain ⟨k, hk, hx⟩ := (hp i x).mp ((he i x).mp hi).2
      exact Structure.SuccessorOf.eq hZF.1 hk hj ▸ hx

theorem cons_ne_empty_l {z a s t : M.Domain} (hz : ∀ p, ¬ M.mem p z)
    (h : Cons_d I z a s t) : t ≠ z := by
  intro e
  obtain ⟨p, _, hp⟩ := (h.2 z a).mpr (Or.inl ⟨rfl, rfl⟩)
  exact hz p (e ▸ hp)

/-- 加首项后的节点直接接在根上，当且仅当其尾列为空。 -/
theorem cons_root_l (hZF : M.Models ZF) {ω A z a s t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) (hzω : M.mem z ω)
    (ha : M.mem a ω) (hs : M.mem s A) (ht : Cons_d I z a s t) : Step_d I ω z t ↔ s = z := by
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨k, hk, hkn, htf⟩ := cons_type_l I hZF hω hz ha hn hs ht
  rw [tree_step_iff_l I hZF hω hzω hk (ds_empty_fun_l I hz) htf]
  constructor
  · rintro ⟨hkz, _⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem hn) hkn hkz
    exact tree_empty_domain_l I hZF.1 hz (e ▸ hs)
  · intro e
    have en := hs.2.1.eq hZF.1 (e.symm ▸ (ds_empty_fun_l I (X := ω) hz).2.1)
    exact ⟨en.trans e ▸ hkn, fun p hp => (hz p hp).elim⟩

end PPAC.Migration.ExistingTreeAddresses
