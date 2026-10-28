/- Exact necessary donor proofs from YesMetaZFC 7979336, for pinned
DiagramOrder.HeightCost.directed_cofinal_sequence / ConeIdeal.countable_cofinal_sequence.
Only enclosing namespace/imports and two qualified intra-slice references differ.
Existing uniformize_formula_l and models_zf_l are reused without duplication. -/
import PPAC.Migration.ExistingSmallUnion
import YesMetaZFC.SetTheory.Ord.Recursion
import PPAC.Companion.YesMetaZFC.SetTheory.Definitional.Project.Predicate

namespace PPAC.Migration.ExistingIndexedChoice
open YesMetaZFC SetTheory
open SetTheory.Definitional.Project
open SetTheory.ZF (exists_setFunctionFromTo_of_denote separation_exists_d)
open PPAC.Migration.ExistingSmallUnion (models_zf_l uniformize_formula_l)
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Next_d (F a x y : M.Domain) : Prop := M.PairMember I x y F ∨
  ((¬ ∃ z, M.PairMember I x z F) ∧ y = a)

def next_m (𝒞 : OrderedPairConvention) {n} (F a x y : Term n) : Formula 1 n :=
  .disj (Formula.orderedPairMem 𝒞 x y F) (.conj
    (.neg (.existsE (Formula.orderedPairMem 𝒞 x.weaken .newest F.weaken))) (Formula.extensionalEq y a))
derive_free_closed next_m

def iter_m (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .disj (.conj (Formula.isZeroLengthSequence 𝒞 (.bound 1))
    (Formula.extensionalEq .newest (.bound 2))) (.disj (.existsE
      (.conj (Formula.isSuccessorLengthSequenceWithLast 𝒞 (.bound 2) .newest)
        (next_m 𝒞 (.bound 4) (.bound 3) .newest (.bound 1))))
      (Formula.isLimitLengthSequenceWithUnion 𝒞 (.bound 1) .newest))

theorem iter_sat_l (hE : Extensional M) (ρ : Env M 2) (s x : M.Domain) :
    (iter_m 𝒞).denote ρ s x ↔ M.IsZeroSuccessorLimitStep I
      (fun x => x = ρ.bound 0) (Next_d I (ρ.bound 1) (ρ.bound 0)) s x := by
  simp only [iter_m, BinarySchema.denote, Structure.IsZeroSuccessorLimitStep, next_m, Next_d,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_isZeroLengthSequence_iff I hE,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff I hE,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff I hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE]
  rfl

/-- 内部自映射从任意初值出发，产生沿模型自身 ω 迭代的函数图。 -/
theorem iterate_l (hZF : M.Models ZF) {ω X F a : M.Domain} (hω : M.IsOmega ω)
    (hF : M.IsSetFunctionFromTo I F X X) (ha : M.mem a X) :
    ∃ g, M.IsSetFunctionFromTo I g ω X ∧
      (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e a g) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x g → M.PairMember I j y g →
        M.PairMember I x y F := by
  classical
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push a
  have hop : M.IsClassFunctionOnTransfiniteSequences I ((iter_m 𝒞).denote ρ) := by
    have ht := ZF.zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences hZF I
      (fun x => x = a) (Next_d I F a) ⟨a, rfl, fun _ h => h⟩ (by
        intro x
        by_cases hn : ∃ y, M.PairMember I x y F
        · obtain ⟨y, hy⟩ := hn
          exact ⟨y, Or.inl hy, fun z hz => hz.elim
            (fun hz => hF.1.2 x z y hz hy) (fun hz => False.elim (hz.1 ⟨y, hy⟩))⟩
        · exact ⟨a, Or.inr ⟨hn, rfl⟩, fun y hy => hy.elim
            (fun hy => False.elim (hn ⟨y, hy⟩)) And.right⟩)
    intro s hs
    obtain ⟨x, hx, hu⟩ := ht s hs
    exact ⟨x, (iter_sat_l I hZF.1 ρ s x).mpr hx,
      fun y hy => hu y ((iter_sat_l I hZF.1 ρ s y).mp hy)⟩
  obtain ⟨g, hg⟩ := ZF.recursiveSequence_exists hZF I ρ (iter_m 𝒞) hop (hω.isOrdinal hZF)
  have hz e (he : ∀ x, ¬ M.mem x e) x (hx : M.PairMember I e x g) : x = a := by
    have heω := (hg.1.2.2 e).mpr ⟨x, hx⟩
    obtain ⟨s, hs, hop⟩ := hg.2 e heω x hx
    have hs0 : M.IsZeroLengthSequence I s := ⟨e, hg.1.restriction heω hs, he⟩
    rcases (iter_sat_l I hZF.1 ρ s x).mp hop with hx | ⟨y, hy, _⟩ | hx
    · exact hx.2
    · exact False.elim (hs0.not_successorLength hZF.1 hy)
    · exact False.elim (hs0.not_limitLength hZF.1 hx)
  have hs i j x y (hij : M.SuccessorOf j i) (hx : M.PairMember I i x g)
      (hy : M.PairMember I j y g) (hxX : M.mem x X) : M.PairMember I x y F := by
    have hi := (hg.1.2.2 i).mpr ⟨x, hx⟩
    have hj := (hg.1.2.2 j).mpr ⟨y, hy⟩
    obtain ⟨s, hs, hop⟩ := hg.2 j hj y hy
    have hsl : M.IsSuccessorLengthSequenceWithLast I s x :=
      ⟨i, hg.1.1.mem hi, j, hij, hg.1.restriction hj hs,
        (hs.2 i x).mpr ⟨hij.predecessor_mem, hx⟩⟩
    rcases (iter_sat_l I hZF.1 ρ s y).mp hop with hy | ⟨z, hz, hy⟩ | hy
    · exact False.elim (hy.1.not_successorLength hZF.1 hsl)
    · have he := hz.last_eq hZF.1 hsl
      subst z
      exact hy.elim id (fun hy => False.elim (hy.1 ((hF.2.2 x hxX).elim fun z hz => ⟨z, hz.2⟩)))
    · exact False.elim (hsl.not_limitLength hZF.1 hy)
  have htarget : ∀ i, M.mem i ω → ∀ x, M.PairMember I i x g → M.mem x X := by
    apply hω.induction (fun i => ∀ x, M.PairMember I i x g → M.mem x X)
    · let φ : UnarySchema 2 := {
        body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
          (.mem .newest (.bound 3))) }
      obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ
        ((⟨fun _ => X, fun _ => X⟩ : Env M 1).push g) ω
      refine ⟨T, fun i => ?_⟩
      rw [hT i]
      simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
      rfl
    · intro e he x hx
      exact hz e he x hx ▸ ha
    · intro i hi ih j hij y hy
      obtain ⟨x, hx⟩ := (hg.1.2.2 i).mp hi
      exact hF.output_mem_of_pairMember (hs i j x y hij hx hy (ih x hx))
  refine ⟨g, ⟨hg.1.2.1, hg.1.2.2, fun i hi => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hg.1.2.2 i).mp hi
    exact ⟨x, htarget i hi x hx, hx⟩
  · intro e he
    obtain ⟨e', he', heω⟩ := hω.1.1
    have heq : e' = e := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he x))
    subst e'
    obtain ⟨x, hx⟩ := (hg.1.2.2 e).mp heω
    exact hz e he x hx ▸ hx
  · intro i j x y hij hx hy
    exact hs i j x y hij hx hy (htarget i ((hg.1.2.2 i).mpr ⟨x, hx⟩) x hx)

theorem indexed_iteration_l (hZF : M.Models ZF) {ω X D F a} (hω : M.IsOmega ω)
    (hD : M.IsCartesianProduct I D ω X) (hF : M.IsSetFunctionFromTo I F D X) (ha : M.mem a X) :
    ∃ Q, M.IsSetFunctionFromTo I Q ω X ∧
      (∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o a Q) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x Q → M.PairMember I j y Q →
        ∃ p, I.Codes p i x ∧ M.PairMember I p y F := by
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let ψ : BinarySchema 1 := {
    body := .existsE (.existsE (.existsE (.existsE
      (.conj (𝒞.code (.bound 5) (.bound 3) (.bound 2))
        (.conj (𝒞.code (.bound 4) (.bound 1) .newest)
          (.conj (Formula.isSuccessor (.bound 1) (.bound 3))
            (Formula.orderedPairMem 𝒞 (.bound 5) .newest (.bound 6)))))))) }
  have hψ s t : ψ.denote ρ s t ↔ ∃ i x j y,
      I.Codes s i x ∧ I.Codes t j y ∧ M.SuccessorOf j i ∧ M.PairMember I s y F := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨R, hR, hr⟩ := exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := D) (target := D) (by
    intro s hsD
    obtain ⟨i, hi, x, _, hs⟩ := (hD s).mp hsD
    obtain ⟨y, _, hsy⟩ := hF.2.2 s hsD
    obtain ⟨j, hj, _⟩ := hω.1.2 i hi
    obtain ⟨t, ht⟩ := I.total j y
    exact ⟨t, (hψ s t).mpr ⟨i, x, j, y, hs, ht, hj, hsy⟩⟩) (by
    intro s _ t u ht hu
    obtain ⟨i, x, j, y, hs, ht, hj, hy⟩ := (hψ s t).mp ht
    obtain ⟨i', x', j', y', hs', hu, hj', hy'⟩ := (hψ s u).mp hu
    obtain ⟨rfl, rfl⟩ := I.injective hs hs'
    have hej := Structure.SuccessorOf.eq hZF.1 hj hj'
    have hey := hF.1.2 s y y' hy hy'
    subst j' y'
    exact I.unique ht hu) (by
    intro s t hsD ht
    obtain ⟨i, x, j, y, hs, ht, hj, hy⟩ := (hψ s t).mp ht
    obtain ⟨i', hi, x', _, hs'⟩ := (hD s).mp hsD
    obtain ⟨rfl, rfl⟩ := I.injective hs hs'
    obtain ⟨j', hj', hjω⟩ := hω.1.2 i hi
    have hej := Structure.SuccessorOf.eq hZF.1 hj' hj
    exact (hD t).mpr ⟨j, hej ▸ hjω, y, hF.output_mem_of_pairMember hy, ht⟩)
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  obtain ⟨s, hs⟩ := I.total o a
  obtain ⟨G, hG, hz, hg⟩ := iterate_l I hZF hω hR ((hD s).mpr ⟨o, hoω, a, ha, hs⟩)
  have coords : ∀ i, M.mem i ω → ∀ s, M.PairMember I i s G → ∃ x, I.Codes s i x := by
    apply hω.induction (fun i => ∀ s, M.PairMember I i s G → ∃ x, I.Codes s i x)
    · let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
      let θ : UnarySchema 1 := {
        body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
          (.existsE (𝒞.code (.bound 1) (.bound 2) .newest))) }
      obtain ⟨C, hC⟩ := separation_exists_d hZF θ δ ω
      exact ⟨C, fun i => by simpa only [θ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, I.realizes] using! hC i⟩
    · intro e he t het
      have heo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (ho x))
      have hts := hG.1.2 e t s het (hz e he)
      exact ⟨a, hts.symm ▸ heo.symm ▸ hs⟩
    · intro i hi ih j hij t hjt
      obtain ⟨r, _, hir⟩ := hG.2.2 i hi
      obtain ⟨x, hri⟩ := ih r hir
      obtain ⟨i', x', j', y, hr', ht', hji, _⟩ := (hψ r t).mp ((hr r t).mp (hg i j r t hij hir hjt)).2
      obtain ⟨hei, _⟩ := I.injective hri hr'
      subst i'
      have hej := Structure.SuccessorOf.eq hZF.1 hji hij
      exact ⟨y, hej ▸ ht'⟩
  let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let θ : BinarySchema 1 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (𝒞.code .newest (.bound 2) (.bound 1))) }
  have hθ i x : θ.denote δ i x ↔ ∃ s, M.PairMember I i s G ∧ I.Codes s i x := by
    simp only [BinarySchema.denote, θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, I.realizes]
    rfl
  obtain ⟨Q, hQ, hq⟩ := exists_setFunctionFromTo_of_denote hZF I θ δ (source := ω) (target := X) (by
    intro i hi
    obtain ⟨s, _, his⟩ := hG.2.2 i hi
    obtain ⟨x, hs⟩ := coords i hi s his
    exact ⟨x, (hθ i x).mpr ⟨s, his, hs⟩⟩) (by
    intro i _ x y hx hy
    obtain ⟨s, his, hs⟩ := (hθ i x).mp hx
    obtain ⟨t, hit, ht⟩ := (hθ i y).mp hy
    have he := hG.1.2 i s t his hit
    exact (I.injective hs (he.symm ▸ ht)).2) (by
    intro i x _ hx
    obtain ⟨s, his, hs⟩ := (hθ i x).mp hx
    obtain ⟨j, _, y, hy, hs'⟩ := (hD s).mp (hG.output_mem_of_pairMember his)
    exact (I.injective hs' hs).2 ▸ hy)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro e he
    have heo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (ho x))
    exact (hq e a).mpr ⟨heo.symm ▸ hoω, (hθ e a).mpr ⟨s, hz e he, heo.symm ▸ hs⟩⟩
  · intro i j x y hij hix hjy
    obtain ⟨s, his, hs⟩ := (hθ i x).mp ((hq i x).mp hix).2
    obtain ⟨t, hjt, ht⟩ := (hθ j y).mp ((hq j y).mp hjy).2
    obtain ⟨i', x', j', y', hs', ht', _, hsy⟩ := (hψ s t).mp ((hr s t).mp (hg i j s t hij his hjt)).2
    obtain ⟨_, hey⟩ := I.injective ht' ht
    exact ⟨s, hs, hey ▸ hsy⟩

theorem indexed_choice_l (hZFC : M.Models ZFC) {n} (φ : UnarySchema (n+2)) (ρ : Env M n)
    {ω X a} (hω : M.IsOmega ω) (ha : M.mem a X)
    (ht : ∀ i x, M.mem i ω → M.mem x X → ∃ y, M.mem y X ∧ φ.denote ((ρ.push i).push x) y) :
    ∃ F, M.IsSetFunctionFromTo I F ω X ∧
      (∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o a F) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x F → M.PairMember I j y F →
        φ.denote ((ρ.push i).push x) y := by
  have hZF := models_zf_l hZFC
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I ω X
  let e : Fin (n+2) → Term (n+4) := Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+4, by omega⟩))
  have he : ∀ i, (e i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  let ψ : BinarySchema n := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest) (pred_m φ e (.bound 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, he] }
  have hψ p y : ψ.denote ρ p y ↔ ∃ i x, I.Codes p i x ∧ φ.denote ((ρ.push i).push x) y := by
    have henv i x : (⟨fun k => (e k).eval ((((ρ.push p).push y).push i).push x),
        ((((ρ.push p).push y).push i).push x).free⟩ : Env M (n+2)) = (ρ.push i).push x := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, pred_sat_l M, henv]
    rfl
  obtain ⟨K, hK, hk⟩ := uniformize_formula_l I hZFC ψ ρ (X := D) (Y := X) (by
    intro p hp
    obtain ⟨i, hi, x, hx, hp⟩ := (hD p).mp hp
    obtain ⟨y, hy, hxy⟩ := ht i x hi hx
    exact ⟨y, hy, (hψ p y).mpr ⟨i, x, hp, hxy⟩⟩)
  obtain ⟨F, hF, hz, hs⟩ := indexed_iteration_l I hZF hω hD hK ha
  refine ⟨F, hF, hz, fun i j x y hij hix hjy => ?_⟩
  obtain ⟨p, hp, hpy⟩ := hs i j x y hij hix hjy
  obtain ⟨i', x', hp', hxy⟩ := (hψ p y).mp (hk p y hpy)
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  exact hxy


end PPAC.Migration.ExistingIndexedChoice
