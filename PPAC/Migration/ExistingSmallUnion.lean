/- Selected EXACT theorem types/proof bodies from YesMetaZFC 7979336:
Choice selector, bounded formula uniformization, and small-family union bound.
Only enclosing namespaces/imports differ. Source object ZFC stays EXPLICIT;
no object Choice premise is added to constructing the directed limit itself. -/
import PPAC.Migration.ConstructionProbeCardinality
import YesMetaZFC.SetTheory.Axioms.ZFC
import YesMetaZFC.SetTheory.ProductConstruction

namespace PPAC.Migration.ExistingSmallUnion
open YesMetaZFC SetTheory
open SetTheory.Definitional.Project
universe u
section Choice
variable {M : Structure.{u}} (h : M.Models ZFC)
include h

-- BEGIN DONOR Choice.Selector
theorem models_zf_l : M.Models ZF := ⟨h.1, fun s hs => h.2 s (.zf hs)⟩

theorem choice_set_l (A : M.Domain)
    (hn : ∀ a, M.mem a A → ∃ x, M.mem x a)
    (hd : ∀ a, M.mem a A → ∀ b, M.mem b A → a ≠ b → ¬ ∃ x, M.mem x a ∧ M.mem x b) :
    ∃ C, ∀ a, M.mem a A → ∃ x, (M.mem x C ∧ M.mem x a) ∧
      ∀ y, (M.mem y C ∧ M.mem y a) → y = x := by
  have hc := (Structure.satisfiesSentence_iff M Axioms.choice).mp (h.2 _ .choice) (fun _ => A)
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq h.1, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken] at hc
  exact hc A ⟨hn, hd⟩

/-- 原选择集公理给出一个模型内关系，为源集的每个非空内部子集唯一选值。 -/
theorem selector_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ C, ∀ T, M.MemberSubset T S → (∃ x, M.mem x T) →
      ∃ x, M.mem x T ∧ M.PairMember I T x C ∧
        ∀ y, M.mem y T → M.PairMember I T y C → y = x := by
  let hZF := models_zf_l h
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF S
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I P S
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF X
  let φ : UnarySchema 1 := {
    body := .existsE (.conj (.mem .newest (.bound 2))
      (.conj (.existsE (.mem .newest (.bound 1)))
        (Formula.isCartesianRow 𝒞 (.bound 1) .newest .newest))) }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ Q
  have ha a : M.mem a A ↔ M.mem a Q ∧ ∃ T, M.mem T P ∧
      (∃ x, M.mem x T) ∧ ∀ p, M.mem p a ↔ ∃ x, M.mem x T ∧ I.Codes p T x := by
    rw [hA a]
    simp only [φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_isCartesianRow_iff I]
    rfl
  obtain ⟨C, hC⟩ := choice_set_l h A (by
    intro a haA
    obtain ⟨_, T, _, ⟨x, hx⟩, ht⟩ := (ha a).mp haA
    obtain ⟨p, hp⟩ := I.total T x
    exact ⟨p, (ht p).mpr ⟨x, hx, hp⟩⟩) (by
    intro a haA b hbA hn ⟨p, hpa, hpb⟩
    obtain ⟨_, T, _, _, ht⟩ := (ha a).mp haA
    obtain ⟨_, V, _, _, hv⟩ := (ha b).mp hbA
    obtain ⟨x, _, hx⟩ := (ht p).mp hpa
    obtain ⟨y, _, hy⟩ := (hv p).mp hpb
    obtain ⟨rfl, _⟩ := I.injective hx hy
    exact hn (h.1.eq_of_same_members a b (fun q => (ht q).trans (hv q).symm)))
  refine ⟨C, fun T hT hn => ?_⟩
  obtain ⟨a, ht⟩ := ZF.exists_cartesianRow hZF I T T
  have htP := (hP T).mpr hT
  have haA : M.mem a A := (ha a).mpr ⟨(hQ a).mpr (by
    intro p hp
    obtain ⟨x, hx, hc⟩ := (ht p).mp hp
    exact (hX p).mpr ⟨T, htP, x, hT x hx, hc⟩), T, htP, hn, ht⟩
  obtain ⟨p, ⟨hpC, hpa⟩, hp⟩ := hC a haA
  obtain ⟨x, hx, hc⟩ := (ht p).mp hpa
  refine ⟨x, hx, ⟨p, hc, hpC⟩, fun y hy ⟨q, hq, hqC⟩ => ?_⟩
  have he := hp q ⟨hqC, (ht q).mpr ⟨y, hy, hq⟩⟩
  exact (I.injective (he ▸ hq) hc).2
-- END DONOR Choice.Selector

end Choice

section Uniformization
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

-- BEGIN DONOR DependentChoice.Uniformize
theorem uniformize_l (hZFC : M.Models ZFC) {X Y R : M.Domain}
    (ht : ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ M.PairMember I x y R) :
    ∃ F, M.IsSetFunctionFromTo I F X Y ∧
      ∀ x y, M.PairMember I x y F → M.PairMember I x y R := by
  let hZF := models_zf_l hZFC
  obtain ⟨C, hC⟩ := selector_l hZFC I Y
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push Y).push C
  let φ : BinarySchema 3 := {
    body := .existsE (.conj (.forallE (.iff (.mem .newest (.bound 1))
      (.conj (.mem .newest (.bound 5)) (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 6)))))
      (.conj (.mem (.bound 1) .newest) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3)))) }
  have hφ x y : φ.denote ρ x y ↔ ∃ T,
      (∀ z, M.mem z T ↔ M.mem z Y ∧ M.PairMember I x z R) ∧
        M.mem y T ∧ M.PairMember I T y C := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have htotal x (hx : M.mem x X) : ∃ y, φ.denote ρ x y := by
    let ψ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2) }
    obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF ψ
      ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push x) Y
    have hT z : M.mem z T ↔ M.mem z Y ∧ M.PairMember I x z R := by
      rw [hT z]
      simp only [ψ, Formula.satisfies_orderedPairMem_iff I]
      rfl
    obtain ⟨y, hy, hc, _⟩ := hC T (fun z hz => ((hT z).mp hz).1)
      ((ht x hx).elim fun y hy => ⟨y, (hT y).mpr hy⟩)
    exact ⟨y, (hφ x y).mpr ⟨T, hT, hy, hc⟩⟩
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ htotal (by
    intro x hx y z hy hz
    obtain ⟨T, hT, hy, hcy⟩ := (hφ x y).mp hy
    obtain ⟨V, hV, hz, hcz⟩ := (hφ x z).mp hz
    have he := hZFC.1.eq_of_same_members V T (fun w => (hV w).trans (hT w).symm)
    subst V
    obtain ⟨a, _, _, hu⟩ := hC T (fun w hw => ((hT w).mp hw).1) ⟨y, hy⟩
    exact (hu y hy hcy).trans (hu z hz hcz).symm) (by
    intro x y _ hy
    obtain ⟨T, hT, hy, _⟩ := (hφ x y).mp hy
    exact ((hT y).mp hy).1)
  refine ⟨F, hF, fun x y hxy => ?_⟩
  obtain ⟨T, hT, hy, _⟩ := (hφ x y).mp ((he x y).mp hxy).2
  exact ((hT y).mp hy).2

/-- 对实际二元公式直接构造内部选择函数，目标界由调用处给出的集合承载。 -/
theorem uniformize_formula_l (hZFC : M.Models ZFC) {n} (φ : BinarySchema n) (ρ : Env M n)
    {X Y : M.Domain} (ht : ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ φ.denote ρ x y) :
    ∃ F, M.IsSetFunctionFromTo I F X Y ∧ ∀ x y, M.PairMember I x y F → φ.denote ρ x y := by
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) X Y
  obtain ⟨W, hW⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have hx x (hx : M.mem x X) : M.mem x W := (hW x).mpr ⟨X, (hP X).mpr (Or.inl rfl), hx⟩
  have hy y (hy : M.mem y Y) : M.mem y W := (hW y).mpr ⟨Y, (hP Y).mpr (Or.inr rfl), hy⟩
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  obtain ⟨F, hF, hf⟩ := uniformize_l I hZFC (fun x hxX => by
    obtain ⟨y, hyY, hφ⟩ := ht x hxX
    exact ⟨y, hyY, (hr x y).mpr ⟨hx x hxX, hy y hyY, hφ⟩⟩)
  exact ⟨F, hF, fun x y hxy => ((hr x y).mp (hf x y hxy)).2.2⟩
-- END DONOR DependentChoice.Uniformize

end Uniformization

section Union
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

-- BEGIN DONOR Card.CountableUnion.UnionBound
theorem union_bound_l (hZFC : M.Models ZFC) {κ A U W : M.Domain}
    (hA : M.CardinalLessOrEqual I A κ) (hU : M.IsUnionOf U A)
    (hc : ∀ T, M.mem T A → M.CardinalLessOrEqual I T κ)
    (hW : M.IsCartesianProduct I W κ κ) : M.CardinalLessOrEqual I U W := by
  obtain ⟨f, hf⟩ := hA
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U κ
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF P
  let φ : BinarySchema 1 := { body := Formula.isInjectionFromTo 𝒞 .newest (.bound 1) (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  have hφ T j : φ.denote ρ T j ↔ M.IsSetInjectionFromTo I j T κ :=
    Formula.satisfies_isInjectionFromTo_iff I hZF.1 ((ρ.push T).push j) .newest (.bound 1) (.bound 2)
  obtain ⟨G, hG, hg⟩ := uniformize_formula_l I hZFC φ ρ (X := A) (Y := K) (by
    intro T hT
    obtain ⟨j, hj⟩ := hc T hT
    refine ⟨j, (hK j).mpr ?_, (hφ T j).mpr hj⟩
    intro q hq
    obtain ⟨x, n, hcode⟩ := hj.1.1.1 q hq
    have hxn : M.PairMember I x n j := ⟨q, hcode, hq⟩
    exact (hP q).mpr ⟨x, (hU x).mpr ⟨T, hT, hj.1.input_mem_of_pairMember hxn⟩,
      n, hj.1.output_mem_of_pairMember hxn, hcode⟩)
  have hg {T j} (h : M.PairMember I T j G) : M.IsSetInjectionFromTo I j T κ := (hφ T j).mp (hg T j h)
  let δ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push G
  let ψ : BinarySchema 2 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (𝒞.code (.bound 4) (.bound 3) (.bound 2))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 7))
        (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 6))
          (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 2) .newest))))))) }
  have hψ x q : ψ.denote δ x q ↔ ∃ n k T j,
      I.Codes q n k ∧ M.PairMember I T n f ∧ M.PairMember I T j G ∧ M.PairMember I x k j := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨H, hH, hh⟩ := uniformize_formula_l I hZFC ψ δ (X := U) (Y := W) (by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := (hU x).mp hx
    obtain ⟨n, hn, hnT⟩ := hf.1.2.2 T hT
    obtain ⟨j, _, hTj⟩ := hG.2.2 T hT
    obtain ⟨k, hk, hxk⟩ := (hg hTj).1.2.2 x hxT
    obtain ⟨q, hq⟩ := I.total n k
    exact ⟨q, (hW q).mpr ⟨n, hn, k, hk, hq⟩, (hψ x q).mpr ⟨n, k, T, j, hq, hnT, hTj, hxk⟩⟩)
  have hinj : M.IsSetInjectionFromTo I H U W := by
    refine ⟨hH, fun x y q hx hy => ?_⟩
    obtain ⟨n, k, T, j, hq, hnT, hTj, hxj⟩ := (hψ x q).mp (hh x q hx)
    obtain ⟨m, l, V, e, hq', hmV, hVe, hye⟩ := (hψ y q).mp (hh y q hy)
    obtain ⟨rfl, rfl⟩ := I.injective hq hq'
    have he := hf.2 T V n hnT hmV
    subst V
    have he := hG.1.2 T j e hTj hVe
    subst e
    exact (hg hTj).2 x y k hxj hye
  exact ⟨H, hinj⟩
-- END DONOR Card.CountableUnion.UnionBound

end Union
end PPAC.Migration.ExistingSmallUnion
