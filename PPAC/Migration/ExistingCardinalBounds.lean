/- Selected proof bodies from YesMetaZFC 7979336 Card/Omega and Card/InfiniteBound.
Only the namespace/import context changes; source hashes and proof-body hashes
are recorded in SOURCE_LOCK. Consumer: pinned OpenAI SupportFilter.inf_mem.
This reuses the donor construction instead of reproving cardinal arithmetic. -/
import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication

namespace PPAC.Migration.ExistingCardinalBounds
open YesMetaZFC SetTheory SetTheory.ZF
open SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

-- BEGIN DONOR Card.Omega
theorem omega_skip_l (hZF : M.Models ZF) {ω i : M.Domain} (hω : M.IsOmega ω) (hi : M.mem i ω) :
    ∃ F, M.IsSetInjectionFromTo I F ω ω ∧ ∀ x, ¬ M.PairMember I x i F := by
  classical
  let φ : BinarySchema 1 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 1)))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.isSuccessor .newest (.bound 1))) }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have hφ x y : φ.denote ρ x y ↔ (M.mem x i ∧ y = x) ∨ (¬ M.mem x i ∧ M.SuccessorOf y x) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isSuccessor_iff]
    rfl
  obtain ⟨F, hF, he⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω) (by
    intro x hx
    by_cases hxi : M.mem x i
    · exact ⟨x, (hφ x x).mpr (Or.inl ⟨hxi, rfl⟩)⟩
    · obtain ⟨y, hy, _⟩ := hω.1.2 x hx
      exact ⟨y, (hφ x y).mpr (Or.inr ⟨hxi, hy⟩)⟩) (by
    intro x _ y z hy hz
    rcases (hφ x y).mp hy with hy | hy <;> rcases (hφ x z).mp hz with hz | hz
    · exact hy.2.trans hz.2.symm
    · exact False.elim (hz.1 hy.1)
    · exact False.elim (hy.1 hz.1)
    · exact Structure.SuccessorOf.eq hZF.1 hy.2 hz.2) (by
    intro x y hx hy
    rcases (hφ x y).mp hy with hy | hy
    · exact hy.2 ▸ hx
    · obtain ⟨z, hz, hzω⟩ := hω.1.2 x hx
      exact Structure.SuccessorOf.eq hZF.1 hy.2 hz ▸ hzω)
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · intro x y z hx hy
    have hxω := hF.input_mem_of_pairMember hx
    have hyω := hF.input_mem_of_pairMember hy
    rcases (hφ x z).mp ((he x z).mp hx).2 with hx | hx <;>
      rcases (hφ y z).mp ((he y z).mp hy).2 with hy | hy
    · exact hx.2.symm.trans hy.2
    · have hyz := hy.2.predecessor_mem
      exact False.elim (hy.1 ((hω.members_areOrdinals hZF i hi).transitive x hx.1 y (hx.2 ▸ hyz)))
    · have hxz := hx.2.predecessor_mem
      exact False.elim (hx.1 ((hω.members_areOrdinals hZF i hi).transitive y hy.1 x (hy.2 ▸ hxz)))
    · exact Structure.SuccessorOf.predecessor_eq hZF.1 (hω.members_areOrdinals hZF x hxω) hx.2 hy.2
  · intro x hx
    rcases (hφ x i).mp ((he x i).mp hx).2 with hx | hx
    · exact (hω.isOrdinal hZF).wellOrder.linear.irrefl i hi (hx.2.symm ▸ hx.1)
    · exact hx.1 hx.2.predecessor_mem

theorem omega_not_le_finite_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) :
    ∀ n, M.mem n ω → ¬ M.CardinalLessOrEqual I ω n := by
  classical
  apply hω.induction (fun n => ¬ M.CardinalLessOrEqual I ω n)
  · let φ : UnarySchema 1 := { body := .neg (Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest) }
    obtain ⟨T, hT⟩ := separation_exists_d hZF φ (⟨fun _ => ω, fun _ => ω⟩ : Env M 1) ω
    refine ⟨T, fun n => ?_⟩
    rw [hT n]
    simp only [φ, Formula.satisfies_neg_iff, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  · intro e he ⟨F, hF⟩
    obtain ⟨o, _, ho⟩ := hω.1.1
    obtain ⟨x, hx, _⟩ := hF.1.2.2 o ho
    exact he x hx
  · intro n hn ih s hs ⟨F, hF⟩
    by_cases hhit : ∃ i, M.PairMember I i n F
    · obtain ⟨i, hi⟩ := hhit
      obtain ⟨G, hG, hGi⟩ := omega_skip_l I hZF hω (hF.1.input_mem_of_pairMember hi)
      obtain ⟨H, hH, he⟩ := exists_compositionFunction hZF I hG.1 hF.1
      have hinj : M.IsSetInjective I H := by
        intro x y v hx hy
        obtain ⟨_, a, hxa, hav⟩ := (he x v).mp hx
        obtain ⟨_, b, hyb, hbv⟩ := (he y v).mp hy
        have hab := hF.2 a b v hav hbv
        exact hG.2 x y a hxa (hab ▸ hyb)
      apply ih
      refine ⟨H, ⟨hH.1, hH.2.1, fun x hx => ?_⟩, hinj⟩
      obtain ⟨y, hy, hxy⟩ := hH.2.2 x hx
      rcases (hs y).mp hy with hyn | heq
      · exact ⟨y, hyn, hxy⟩
      · have heq := hZF.1.eq_of_same_members y n heq
        subst y
        obtain ⟨_, a, hxa, han⟩ := (he x n).mp hxy
        have hai := hF.2 a i n han hi
        exact False.elim (hGi x (hai ▸ hxa))
    · apply ih
      refine ⟨F, ⟨hF.1.1, hF.1.2.1, fun x hx => ?_⟩, hF.2⟩
      obtain ⟨y, hy, hxy⟩ := hF.1.2.2 x hx
      rcases (hs y).mp hy with hyn | heq
      · exact ⟨y, hyn, hxy⟩
      · exact False.elim (hhit ⟨x, hZF.1.eq_of_same_members y n heq ▸ hxy⟩)

/-- ω 的基数性由原 ZF 自动取得，不再要求调用者另行给出。 -/
theorem omega_cardinal_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) : M.IsCardinal I ω := by
  refine ⟨hω.isOrdinal hZF, fun n hn he => ?_⟩
  obtain ⟨F, hF⟩ := he.symm hZF I
  exact omega_not_le_finite_l I hZF hω n hn ⟨F, hF.1⟩

-- END DONOR Card.Omega

-- BEGIN DONOR Card.InfiniteBound
theorem infinite_product_l (hZF : M.Models ZF) {ω κ X Y W} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hX : M.CardinalLessOrEqual I X κ) (hY : M.CardinalLessOrEqual I Y κ)
    (hW : M.IsCartesianProduct I W X Y) : M.CardinalLessOrEqual I W κ := by
  obtain ⟨S, hS⟩ := exists_cartesianProduct hZF I κ κ
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  obtain ⟨F, hF⟩ := exists_cartesianProductInjection hZF I hW hS hf hg
  have hωc := omega_cardinal_l I hZF hω
  obtain ⟨G, hG⟩ := cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hκ.1, Structure.Equinumerous.refl hZF I κ⟩ hS (infiniteCardinal_selfMultiplication hZF I hω hωc hκ)
  exact exists_compositionInjection hZF I hF hG

/-- 两个 κ 小集的实际并仍为 κ 小集；重叠部分统一使用左侧编号。 -/
theorem infinite_union_two_l (hZF : M.Models ZF) {ω κ X Y U} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hX : M.CardinalLessOrEqual I X κ) (hY : M.CardinalLessOrEqual I Y κ)
    (hU : M.IsUnionOfTwo U X Y) : M.CardinalLessOrEqual I U κ := by
  classical
  obtain ⟨F, hF⟩ := hX
  obtain ⟨G, hG⟩ := hY
  have hwκ := hω.subset_limitOrdinal hZF
    (infiniteCardinal_isLimitOrdinal hZF I hω (omega_cardinal_l I hZF hω) hκ)
  obtain ⟨e, he, heω⟩ := hω.1.1
  obtain ⟨l, hl, hlω⟩ := hω.1.2 e heω
  have hne : e ≠ l := by intro hh; subst l; exact he e hl.predecessor_mem
  obtain ⟨W, hW⟩ := exists_cartesianProduct hZF I κ κ
  let ρ : Env M 5 := ((((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push X).push e).push l
  let φ : BinarySchema 5 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 4)) (.existsE
      (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 7)) (𝒞.code (.bound 1) (.bound 4) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (.existsE
        (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 6)) (𝒞.code (.bound 1) (.bound 3) .newest)))) }
  have hφ x p : φ.denote ρ x p ↔
      (M.mem x X ∧ ∃ n, M.PairMember I x n F ∧ I.Codes p e n) ∨
      (¬ M.mem x X ∧ ∃ n, M.PairMember I x n G ∧ I.Codes p l n) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  obtain ⟨H, hH⟩ := exists_setInjectionFromTo_of_denote hZF I φ ρ (source := U) (target := W) (by
    intro x hx
    by_cases hxx : M.mem x X
    · obtain ⟨n, _, hxn⟩ := hF.1.2.2 x hxx
      obtain ⟨p, hp⟩ := I.total e n
      exact ⟨p, (hφ x p).mpr (Or.inl ⟨hxx, n, hxn, hp⟩)⟩
    · obtain ⟨n, _, hxn⟩ := hG.1.2.2 x (((hU x).mp hx).resolve_left hxx)
      obtain ⟨p, hp⟩ := I.total l n
      exact ⟨p, (hφ x p).mpr (Or.inr ⟨hxx, n, hxn, hp⟩)⟩) (by
    intro x _ p q hp hq
    rcases (hφ x p).mp hp with ⟨hx, n, hn, hp⟩ | ⟨hx, n, hn, hp⟩ <;>
      rcases (hφ x q).mp hq with ⟨hy, m, hm, hq⟩ | ⟨hy, m, hm, hq⟩
    · have he := hF.1.1.2 x n m hn hm
      subst m
      exact I.unique hp hq
    · exact False.elim (hy hx)
    · exact False.elim (hx hy)
    · have he := hG.1.1.2 x n m hn hm
      subst m
      exact I.unique hp hq) (by
    intro x p _ hp
    rcases (hφ x p).mp hp with ⟨_, n, hn, hp⟩ | ⟨_, n, hn, hp⟩
    · exact (hW p).mpr ⟨e, hwκ e heω, n, hF.1.output_mem_of_pairMember hn, hp⟩
    · exact (hW p).mpr ⟨l, hwκ l hlω, n, hG.1.output_mem_of_pairMember hn, hp⟩) (by
    intro x y p _ _ hx hy
    rcases (hφ x p).mp hx with ⟨_, n, hn, hp⟩ | ⟨_, n, hn, hp⟩ <;>
      rcases (hφ y p).mp hy with ⟨_, m, hm, hp'⟩ | ⟨_, m, hm, hp'⟩
    · obtain ⟨_, hnm⟩ := I.injective hp hp'
      subst m
      exact hF.2 x y n hn hm
    · exact False.elim (hne (I.injective hp hp').1)
    · exact False.elim (hne (I.injective hp hp').1.symm)
    · obtain ⟨_, hnm⟩ := I.injective hp hp'
      subst m
      exact hG.2 x y n hn hm)
  obtain ⟨J, hJ⟩ := exists_identityBijection hZF I κ
  obtain ⟨K, hK⟩ := infinite_product_l I hZF hω hκ ⟨J, hJ.1⟩ ⟨J, hJ.1⟩ hW
  exact exists_compositionInjection hZF I hH hK

-- END DONOR Card.InfiniteBound

end PPAC.Migration.ExistingCardinalBounds
