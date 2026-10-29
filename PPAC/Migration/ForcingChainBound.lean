/- Pinned AssignedGraphs.ChainBound.cardinal_le/cardinal_le_mul:484-525.
The source relation is represented by the internal graph (p,(a,b)).
Reuse the donor CCC fiber proof and ExistingSmallUnion uniformization:
all selected maps and all injections are sets of the object model. -/
import PPAC.Migration.ExistingSmallUnion
import PPAC.Migration.ConstructibleSource

namespace PPAC.Migration.ForcingChainBound
open YesMetaZFC SetTheory SetTheory.Definitional.Project
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section Internal
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}
variable (I : 𝒞.Interpretation M)

def Values (R p a b : M.Domain) : Prop :=
  ∃ ab, I.Codes ab a b ∧ M.PairMember I p ab R

def rel {n} (R p a b : Term n) : Formula 1 n :=
  .existsE (.conj (𝒞.code .newest a.weaken b.weaken)
    (Formula.orderedPairMem 𝒞 p.weaken .newest R.weaken))

derive_free_closed rel

theorem rel_semantics {n} (ρ : Env M n) (R p a b : Term n) :
    Formula.satisfies ρ (rel (𝒞 := 𝒞) R p a b) ↔
      Values I (R.eval ρ) (p.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [rel, Values, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

def ChainBound (P C ν : M.Domain) : Prop :=
  ∀ T, M.MemberSubset T P →
    (∀ p, M.mem p T → ∀ q, M.mem q T → M.PairMember I p q C → p = q) →
    M.CardinalLessOrEqual I T ν

/-- The actual range antichain proof, with no host cardinal or chosen map. -/
theorem cardinal_le (hZF : M.Models ZF) {P C ν D c : M.Domain}
    (hrefl : ∀ p, M.mem p P → M.PairMember I p p C)
    (hc : ChainBound I P C ν) (hmap : M.IsSetFunctionFromTo I c D P)
    (hsingle : ∀ x y p q, M.PairMember I x p c → M.PairMember I y q c →
      M.PairMember I p q C → x = y) : M.CardinalLessOrEqual I D ν := by
  obtain ⟨T, hT⟩ := ZF.exists_range_of_setFunction hZF I hmap.1 hmap.2.1
  have hTP : M.MemberSubset T P := by
    intro p hp
    obtain ⟨x, hx⟩ := (hT p).mp hp
    exact hmap.output_mem_of_pairMember hx
  have hanti : ∀ p, M.mem p T → ∀ q, M.mem q T → M.PairMember I p q C → p = q := by
    intro p hp q hq hpq
    obtain ⟨x, hx⟩ := (hT p).mp hp
    obtain ⟨y, hy⟩ := (hT q).mp hq
    exact hmap.1.2 x p q hx (hsingle x y p q hx hy hpq ▸ hy)
  have hinj : M.IsSetInjectionFromTo I c D T := by
    refine ⟨⟨hmap.1, hmap.2.1, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨p, _, hxp⟩ := hmap.2.2 x hx
      exact ⟨p, (hT p).mpr ⟨x, hxp⟩, hxp⟩
    · intro x y p hx hy
      exact hsingle x y p p hx hy (hrefl p (hmap.output_mem_of_pairMember hx))
  obtain ⟨f, hf⟩ := hc T hTP hanti
  exact ZF.exists_compositionInjection hZF I hinj hf

/-- Definable possible-value fiber, before choosing its injection. -/
def Fiber (P R B a D : M.Domain) : Prop :=
  ∀ b, M.mem b D ↔ M.mem b B ∧ ∃ p, M.mem p P ∧ Values I R p a b

def fiber {n} (P R B a D : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest D.weaken) (.conj (.mem .newest B.weaken)
    (.existsE (.conj (.mem .newest P.weaken.weaken)
      (rel (𝒞 := 𝒞) R.weaken.weaken .newest a.weaken.weaken (.bound 1))))))

derive_free_closed fiber

theorem fiber_semantics {n} (ρ : Env M n) (P R B a D : Term n) :
    Formula.satisfies ρ (fiber (𝒞 := 𝒞) P R B a D) ↔
      Fiber I (P.eval ρ) (R.eval ρ) (B.eval ρ) (a.eval ρ) (D.eval ρ) := by
  simp only [fiber, Fiber, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    rel_semantics I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem exists_fiber (hZF : M.Models ZF) (P R B a : M.Domain) :
    ∃ D, Fiber I P R B a D := by
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push a).push P
  let φ : UnarySchema 3 := {body := .existsE (.conj (.mem .newest (.bound 2))
    (rel (𝒞 := 𝒞) (.bound 4) .newest (.bound 3) (.bound 1)))}
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨D, fun b => ?_⟩
  rw [hD b]
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rel_semantics I]
  rfl

theorem fiber_bound (hZFC : M.Models ZFC) {P C ν R B a D : M.Domain}
    (hrefl : ∀ p, M.mem p P → M.PairMember I p p C)
    (hc : ChainBound I P C ν) (hD : Fiber I P R B a D)
    (hsingle : ∀ b b' p q, M.mem b B → M.mem b' B → M.mem p P → M.mem q P →
      Values I R p a b → Values I R q a b' → M.PairMember I p q C → b = b') :
    M.CardinalLessOrEqual I D ν := by
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push a).push P
  let φ : BinarySchema 3 := {body := (.conj (.mem .newest (.bound 2))
    (rel (𝒞 := 𝒞) (.bound 4) .newest (.bound 3) (.bound 1)))}
  have hφ b p : φ.denote ρ b p ↔ M.mem p P ∧ Values I R p a b := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rel_semantics I]
    rfl
  obtain ⟨c, hcmap, hchoose⟩ := ExistingSmallUnion.uniformize_formula_l I hZFC φ ρ
    (X := D) (Y := P) (by
      intro b hb
      obtain ⟨_, p, hp, hR⟩ := (hD b).mp hb
      exact ⟨p, hp, (hφ b p).mpr ⟨hp, hR⟩⟩)
  apply cardinal_le I (ExistingSmallUnion.models_zf_l hZFC) hrefl hc hcmap
  intro b b' p q hb hb' hpq
  obtain ⟨hp, hR⟩ := (hφ b p).mp (hchoose b p hb)
  obtain ⟨hq, hR'⟩ := (hφ b' q).mp (hchoose b' q hb')
  exact hsingle b b' p q ((hD b).mp (hcmap.input_mem_of_pairMember hb)).1
    ((hD b').mp (hcmap.input_mem_of_pairMember hb')).1 hp hq hR hR' hpq

/-- Exact source bound |B| ≤ |A| × ν; A and ν need not coincide. -/
theorem cardinal_le_mul (hZFC : M.Models ZFC) {P C ν R A B W : M.Domain}
    (hrefl : ∀ p, M.mem p P → M.PairMember I p p C)
    (hc : ChainBound I P C ν)
    (htotal : ∀ b, M.mem b B → ∃ a, M.mem a A ∧ ∃ p, M.mem p P ∧ Values I R p a b)
    (hsingle : ∀ a b b' p q, M.mem a A → M.mem b B → M.mem b' B →
      M.mem p P → M.mem q P → Values I R p a b → Values I R q a b' →
      M.PairMember I p q C → b = b')
    (hW : M.IsCartesianProduct I W A ν) : M.CardinalLessOrEqual I B W := by
  have hZF := ExistingSmallUnion.models_zf_l hZFC
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I B ν
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF Q
  let ρ : Env M 4 := (((⟨fun _ => R, fun _ => R⟩ : Env M 1).push P).push B).push ν
  let φ : BinarySchema 4 := {body := .existsE (.conj
    (fiber (𝒞 := 𝒞) (.bound 5) (.bound 6) (.bound 4) (.bound 2) .newest)
    (Formula.isInjectionFromTo 𝒞 (.bound 1) .newest (.bound 3)))}
  have hφ a j : φ.denote ρ a j ↔ ∃ D, Fiber I P R B a D ∧ M.IsSetInjectionFromTo I j D ν := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, fiber_semantics I, Formula.satisfies_isInjectionFromTo_iff I hZF.1]
    rfl
  obtain ⟨G, hG, hg⟩ := ExistingSmallUnion.uniformize_formula_l I hZFC φ ρ (X := A) (Y := K) (by
    intro a ha
    obtain ⟨D, hD⟩ := exists_fiber I hZF P R B a
    obtain ⟨j, hj⟩ := fiber_bound I hZFC hrefl hc hD (hsingle a · · · · ha)
    refine ⟨j, (hK j).mpr ?_, (hφ a j).mpr ⟨D, hD, hj⟩⟩
    intro z hz
    obtain ⟨b, i, hcode⟩ := hj.1.1.1 z hz
    have he : M.PairMember I b i j := ⟨z, hcode, hz⟩
    exact (hQ z).mpr ⟨b, ((hD b).mp (hj.1.input_mem_of_pairMember he)).1,
      i, hj.1.output_mem_of_pairMember he, hcode⟩)
  have hfamily a j (haj : M.PairMember I a j G) := (hφ a j).mp (hg a j haj)
  let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : BinarySchema 1 := {body := .existsE (.existsE (.existsE (.conj
    (𝒞.code (.bound 3) (.bound 2) (.bound 1)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5))
      (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 1) .newest)))))}
  have hψ b z : ψ.denote δ b z ↔ ∃ a i j,
      I.Codes z a i ∧ M.PairMember I a j G ∧ M.PairMember I b i j := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨F, hF, hf⟩ := ExistingSmallUnion.uniformize_formula_l I hZFC ψ δ (X := B) (Y := W) (by
    intro b hb
    obtain ⟨a, ha, p, hp, hR⟩ := htotal b hb
    obtain ⟨j, _, haj⟩ := hG.2.2 a ha
    obtain ⟨D, hD, hj⟩ := hfamily a j haj
    obtain ⟨i, hi, hbi⟩ := hj.1.2.2 b ((hD b).mpr ⟨hb, p, hp, hR⟩)
    obtain ⟨z, hz⟩ := I.total a i
    exact ⟨z, (hW z).mpr ⟨a, ha, i, hi, hz⟩, (hψ b z).mpr ⟨a, i, j, hz, haj, hbi⟩⟩)
  refine ⟨F, hF, ?_⟩
  intro b b' z hb hb'
  obtain ⟨a, i, j, hz, haj, hbi⟩ := (hψ b z).mp (hf b z hb)
  obtain ⟨a', i', j', hz', haj', hbi'⟩ := (hψ b' z).mp (hf b' z hb')
  obtain ⟨rfl, rfl⟩ := I.injective hz hz'
  have he := hG.1.2 a j j' haj haj'
  subst j'
  obtain ⟨D, _, hj⟩ := hfamily a j haj
  exact hj.2 b b' i hbi hbi'

def chainBound {n} (P C ν : Term n) : Formula 1 n :=
  .forallE (.imp (Formula.subset .newest P.weaken)
    (.imp (.forallE (.forallE (.imp (.mem (.bound 1) (.bound 2))
      (.imp (.mem .newest (.bound 2))
        (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest C.weaken.weaken.weaken)
          (Formula.extensionalEq (.bound 1) .newest))))))
      (Formula.cardinalLessOrEqual 𝒞 .newest ν.weaken)))

derive_free_closed chainBound

theorem chainBound_semantics (hE : Extensional M) {n} (ρ : Env M n) (P C ν : Term n) :
    Formula.satisfies ρ (chainBound (𝒞 := 𝒞) P C ν) ↔
      ChainBound I (P.eval ρ) (C.eval ρ) (ν.eval ρ) := by
  simp only [chainBound, ChainBound, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  change (∀ T, M.MemberSubset T (P.eval ρ) →
    (∀ p q, M.mem p T → M.mem q T → M.PairMember I p q (C.eval ρ) → p = q) →
      M.CardinalLessOrEqual I T (ν.eval ρ)) ↔ _
  constructor
  · intro h T hT hanti
    exact h T hT (fun p q hp hq => hanti p hp q hq)
  · intro h T hT hanti
    exact h T hT (fun p hp q hq => hanti p q hp hq)

def compatibleRefl {n} (P C : Term n) : Formula 1 n :=
  .forallE (.imp (.mem .newest P.weaken)
    (Formula.orderedPairMem 𝒞 .newest .newest C.weaken))

derive_free_closed compatibleRefl

def total {n} (P R A B : Term n) : Formula 1 n :=
  .forallE (.imp (.mem .newest B.weaken) (.existsE (.conj (.mem .newest A.weaken.weaken)
    (.existsE (.conj (.mem .newest P.weaken.weaken.weaken)
      (rel (𝒞 := 𝒞) R.weaken.weaken.weaken .newest (.bound 1) (.bound 2)))))))

derive_free_closed total

def single {n} (P C R A B : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 4) A.weaken.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 3) B.weaken.weaken.weaken.weaken.weaken)
        (.imp (.mem (.bound 2) B.weaken.weaken.weaken.weaken.weaken)
          (.imp (.mem (.bound 1) P.weaken.weaken.weaken.weaken.weaken)
            (.imp (.mem .newest P.weaken.weaken.weaken.weaken.weaken)
              (.imp (rel (𝒞 := 𝒞) R.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 4) (.bound 3))
                (.imp (rel (𝒞 := 𝒞) R.weaken.weaken.weaken.weaken.weaken .newest (.bound 4) (.bound 2))
                  (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest C.weaken.weaken.weaken.weaken.weaken)
                    (Formula.extensionalEq (.bound 3) (.bound 2))))))))))))))

derive_free_closed single

/-- Pure membership sentence, retaining all sets and the exact product. -/
def boundSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 7
    (.imp (compatibleRefl (𝒞 := 𝒞) (.bound 0) (.bound 1))
      (.imp (chainBound (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2))
        (.imp (total (𝒞 := 𝒞) (.bound 0) (.bound 3) (.bound 4) (.bound 5))
          (.imp (single (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 3) (.bound 4) (.bound 5))
            (.imp (Formula.isCartesianProduct 𝒞 (.bound 6) (.bound 4) (.bound 2))
              (Formula.cardinalLessOrEqual 𝒞 (.bound 5) (.bound 6)))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
/-- Arbitrary models of object ZFC; no external well-foundedness assumption. -/
theorem bound_models (hZFC : M.Models ZFC) : M.SatisfiesSentence (boundSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, compatibleRefl, total, single,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZFC.1,
    Formula.satisfies_isCartesianProduct_iff I, Formula.satisfies_cardinalLessOrEqual_iff I hZFC.1,
    chainBound_semantics I hZFC.1, rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact fun hrefl hc ht hs hW => cardinal_le_mul I hZFC hrefl hc ht hs hW

end Internal

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

/-- Object choice is discharged by the EXISTING internal L theorem. -/
theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (ConstructibleGround.relative (boundSentence PureKuratowskiProject.convention))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM
  exact bound_models (KuratowskiZF.interpretation (ConstructibleSource.model_zf hM))
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingChainBound
