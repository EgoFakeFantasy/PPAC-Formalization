/- Pinned ConservativeHulls.CountableHull.stage/carrier/countable/closed:177-207.
Adapt the actual internal powerset iteration from YesMetaZFC CountableHull.lean
(donor 79793365c2145c53db37eaf8ab23a64826bd9738, cc_hull_l), with BINARY
multivalued rows as in the source. Reuse the already imported internal countable
product/cover/union and omega-chain proofs. The result retains the actual stage
graph, exact successor operation and union; empty seeds are allowed.
-/
import PPAC.Companion.YesMetaZFC.SetTheory.CountableChain
import PPAC.Migration.ConstructionDirectedCardinality
import PPAC.Migration.ConstructibleSource

namespace PPAC.Migration.ConstructionCountableHull
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.SetTheory
open SetTheory.Definitional.Project
universe u
set_option autoImplicit false
set_option maxRecDepth 8192

section Internal
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- The value of the given binary operation, using its actual pair-indexed graph. -/
def Row (F x y Y : M.Domain) : Prop :=
  ∃ q, I.Codes q x y ∧ M.PairMember I q Y F

def row {n : Nat} (𝒞 : OrderedPairConvention) (F x y Y : Term n) : Formula 1 n :=
  .existsE (.conj (𝒞.code .newest x.weaken y.weaken)
    (Formula.orderedPairMem 𝒞 .newest Y.weaken F.weaken))
derive_free_closed row

theorem row_semantics {n : Nat} (ρ : Env M n) (F x y Y : Term n) :
    Formula.satisfies ρ (row 𝒞 F x y Y) ↔ Row I (F.eval ρ) (x.eval ρ) (y.eval ρ) (Y.eval ρ) := by
  simp only [row, Row, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

def Reach (F A z : M.Domain) : Prop :=
  M.mem z A ∨ ∃ x y Y, M.mem x A ∧ M.mem y A ∧ Row I F x y Y ∧ M.mem z Y

def reach {n : Nat} (𝒞 : OrderedPairConvention) (F A z : Term n) : Formula 1 n :=
  .disj (.mem z A) (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 2) A.weaken.weaken.weaken)
      (.conj (.mem (.bound 1) A.weaken.weaken.weaken)
        (.conj (row 𝒞 F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
          (.mem z.weaken.weaken.weaken .newest)))))))
derive_free_closed reach

theorem reach_semantics {n : Nat} (ρ : Env M n) (F A z : Term n) :
    Formula.satisfies ρ (reach 𝒞 F A z) ↔ Reach I (F.eval ρ) (A.eval ρ) (z.eval ρ) := by
  simp only [reach, Reach, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, row_semantics I,
    Definitional.Term.eval_weaken]
  rfl

def Step (F A C : M.Domain) : Prop := ∀ z, M.mem z C ↔ Reach I F A z

def step {n : Nat} (𝒞 : OrderedPairConvention) (F A C : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest C.weaken) (reach 𝒞 F.weaken A.weaken .newest))
derive_free_closed step

theorem step_semantics {n : Nat} (ρ : Env M n) (F A C : Term n) :
    Formula.satisfies ρ (step 𝒞 F A C) ↔ Step I (F.eval ρ) (A.eval ρ) (C.eval ρ) := by
  simp only [step, Step, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, reach_semantics I, Definitional.Term.eval_weaken]
  rfl

def Closed (F N : M.Domain) : Prop :=
  ∀ x y Y, M.mem x N → M.mem y N → Row I F x y Y → M.MemberSubset Y N

def closed {n : Nat} (𝒞 : OrderedPairConvention) (F N : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) N.weaken.weaken.weaken)
    (.imp (.mem (.bound 1) N.weaken.weaken.weaken)
      (.imp (row 𝒞 F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (Formula.subset .newest N.weaken.weaken.weaken))))))
derive_free_closed closed

theorem closed_semantics {n : Nat} (ρ : Env M n) (F N : Term n) :
    Formula.satisfies ρ (closed 𝒞 F N) ↔ Closed I (F.eval ρ) (N.eval ρ) := by
  simp only [closed, Closed, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, row_semantics I, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  rfl

/-- The actual graph of the source stages, indexed by the model's entire omega. -/
def Stages (ω P F A Q : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I Q ω P ∧
    (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e A Q) ∧
      ∀ i j C D, M.SuccessorOf j i → M.PairMember I i C Q →
        M.PairMember I j D Q → Step I F C D

def stages {n : Nat} (𝒞 : OrderedPairConvention) (ω P F A Q : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 Q ω P)
    (.conj (.forallE (.imp (Formula.isEmpty .newest)
      (Formula.orderedPairMem 𝒞 .newest A.weaken Q.weaken)))
      (.forallE (.forallE (.forallE (.forallE
        (.imp (Formula.isSuccessor (.bound 2) (.bound 3))
          (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) Q.weaken.weaken.weaken.weaken)
            (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest Q.weaken.weaken.weaken.weaken)
              (step 𝒞 F.weaken.weaken.weaken.weaken (.bound 1) .newest)))))))))
derive_free_closed stages

theorem stages_semantics (hE : Extensional M) {n : Nat} (ρ : Env M n)
    (ω P F A Q : Term n) :
    Formula.satisfies ρ (stages 𝒞 ω P F A Q) ↔
      Stages I (ω.eval ρ) (P.eval ρ) (F.eval ρ) (A.eval ρ) (Q.eval ρ) := by
  simp only [stages, Stages, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff,
    step_semantics I, Definitional.Term.eval_weaken]
  rfl

/-- The original binary step preserves internal countability, including A = empty. -/
theorem step_countable (hZFC : M.Models ZFC) {ω X XX P F A C : M.Domain}
    (hω : M.IsOmega ω) (hXX : M.IsCartesianProduct I XX X X)
    (hF : M.IsSetFunctionFromTo I F XX P)
    (hval : ∀ q Y, M.PairMember I q Y F → M.CardinalLessOrEqual I Y ω)
    (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) (hC : Step I F A C) :
    M.CardinalLessOrEqual I C ω := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I A A
  have hk := ZF.countable_product_l I hZF hω ha ha hK
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
      (.disj (Formula.extensionalEq (.bound 2) (.bound 1)) (.existsE
        (.conj (Formula.orderedPairMem 𝒞 (.bound 4) .newest (.bound 5))
          (.mem (.bound 3) .newest)))))) }
  have hφ q z : φ.denote ρ q z ↔ ∃ x y,
      I.Codes q x y ∧ (z = x ∨ ∃ Y, M.PairMember I q Y F ∧ M.mem z Y) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, I.satisfies_code_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
    rfl
  apply ZFC.countable_cover_l I hZFC hω φ ρ hk
  · intro q hq D hD
    obtain ⟨x, hx, y, hy, hqxy⟩ := (hK q).mp hq
    have hqXX := (hXX q).mpr ⟨x, hA x hx, y, hA y hy, hqxy⟩
    obtain ⟨Y, _, hqY⟩ := hF.2.2 q hqXX
    obtain ⟨T, hT⟩ := KP.exists_insert (ZF.modelsKP hZF) Y x
    obtain ⟨f, hf⟩ := ZF.countable_insert_l I hZF hω (hval q Y hqY) hT
    obtain ⟨g, hg⟩ := ZF.exists_inclusionInjection hZF I
      (show M.MemberSubset D T from fun z hz => by
        obtain ⟨x', y', hc, hz⟩ := (hφ q z).mp ((hD z).mp hz).2
        obtain ⟨rfl, rfl⟩ := I.injective hc hqxy
        rcases hz with he | ⟨Z, hqZ, hzZ⟩
        · exact (hT z).mpr (Or.inr he)
        · exact (hT z).mpr (Or.inl (hF.1.2 q Z Y hqZ hqY ▸ hzZ)))
    exact ZF.exists_compositionInjection hZF I hg hf
  · intro z hz
    rcases (hC z).mp hz with hz | ⟨x, y, Y, hx, hy, ⟨q, hq, hqY⟩, hzY⟩
    · obtain ⟨q, hq⟩ := I.total z z
      exact ⟨q, (hK q).mpr ⟨z, hz, z, hz, hq⟩,
        (hφ q z).mpr ⟨z, z, hq, Or.inl rfl⟩⟩
    · exact ⟨q, (hK q).mpr ⟨x, hx, y, hy, hq⟩,
        (hφ q z).mpr ⟨x, y, hq, Or.inr ⟨Y, hqY, hzY⟩⟩⟩

/-- Source CountableHull.carrier with its actual internal stage graph.
The iteration/induction/range/union body is adapted from donor cc_hull_l;
the binary same-stage argument consumes the already migrated ordinal chain. -/
theorem exists_hull (hZFC : M.Models ZFC) {ω X XX P F A : M.Domain}
    (hω : M.IsOmega ω) (hXX : M.IsCartesianProduct I XX X X)
    (hP : M.IsPowerSetOf P X) (hF : M.IsSetFunctionFromTo I F XX P)
    (hval : ∀ q Y, M.PairMember I q Y F → M.CardinalLessOrEqual I Y ω)
    (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ Q N, Stages I ω P F A Q ∧ Cc_union_d I Q N ∧
      M.MemberSubset A N ∧ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧ Closed I F N := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := step 𝒞 (.bound 2) (.bound 1) .newest }
  have hφ C D : φ.denote ρ C D ↔ Step I F C D := step_semantics I _ _ _ _
  have reach_sub {C : M.Domain} (hC : M.MemberSubset C X) {z : M.Domain}
      (hz : Reach I F C z) : M.mem z X := by
    rcases hz with hz | ⟨x, y, Y, _, _, ⟨q, _, hqY⟩, hzY⟩
    · exact hC z hz
    · exact (hP Y).mp (hF.output_mem_of_pairMember hqY) z hzY
  have total C (hCP : M.mem C P) : ∃ D, φ.denote ρ C D := by
    let η := ρ.push C
    let ψ : UnarySchema 2 := { body := reach 𝒞 (.bound 2) (.bound 1) .newest }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ η X
    refine ⟨D, (hφ C D).mpr (fun z => ?_)⟩
    have hs := reach_semantics I (η.push z) (.bound 2) (.bound 1) .newest
    change ψ.denote η z ↔ Reach I F C z at hs
    exact (hD z).trans ((and_congr_right (fun _ => hs)).trans
      ⟨And.right, fun hz => ⟨reach_sub ((hP C).mp hCP) hz, hz⟩⟩)
  obtain ⟨G, hG, hg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := P) (target := P) total
    (fun C _ D E hD hE => hZF.1.eq_of_same_members D E
      (fun z => ((hφ C D).mp hD z).trans ((hφ C E).mp hE z).symm))
    (fun C D hC hD => (hP D).mpr
      (fun z hz => reach_sub ((hP C).mp hC) (((hφ C D).mp hD z).mp hz)))
  obtain ⟨Q, hQ, hz, hs⟩ := ZFC.iterate_l I hZF hω hG ((hP A).mpr hA)
  have succ {i j C D : M.Domain} (hji : M.SuccessorOf j i)
      (hi : M.PairMember I i C Q) (hj : M.PairMember I j D Q) : Step I F C D :=
    (hφ C D).mp ((hg C D).mp (hs i j C D hji hi hj)).2
  have increasing := ZF.cc_increasing_of_successor_l I hZF hω hQ
    (fun i j C D hji hi hj z hzC => (succ hji hi hj z).mpr (Or.inl hzC))
  let η : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push ω
  let ψ : UnarySchema 2 := {
    body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
      (Formula.cardinalLessOrEqual 𝒞 .newest (.bound 2))) }
  have hψ i : ψ.denote η i ↔ ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  have count : ∀ i, M.mem i ω → ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω := by
    apply hω.induction (fun i => ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω)
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ η ω
      exact ⟨D, fun i => (hD i).trans (and_congr_right fun _ => hψ i)⟩
    · intro e he C hC
      exact hQ.1.2 e A C (hz e he) hC ▸ ha
    · intro i hi ih j hji D hj
      obtain ⟨C, hC, hiC⟩ := hQ.2.2 i hi
      exact step_countable I hZFC hω hXX hF hval ((hP C).mp hC) (ih C hiC) (succ hji hiC hj)
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  obtain ⟨N, hN⟩ := KP.exists_union (ZF.modelsKP hZF) Y
  have hu : Cc_union_d I Q N := fun z => (hN z).trans
    ⟨fun ⟨C, hC, hzC⟩ => (hY C).mp hC |>.elim fun i hi => ⟨i, C, hi, hzC⟩,
      fun ⟨i, C, hi, hzC⟩ => ⟨C, (hY C).mpr ⟨i, hi⟩, hzC⟩⟩
  have hQY : M.IsSetFunctionFromTo I Q ω Y := ⟨hQ.1, hQ.2.1, fun i hi => by
    obtain ⟨C, _, hiC⟩ := hQ.2.2 i hi
    exact ⟨C, (hY C).mpr ⟨i, hiC⟩, hiC⟩⟩
  have hy : M.CardinalLessOrEqual I Y ω := ZFC.surjection_bound_l I hZFC hQY (fun C hC => by
    obtain ⟨i, hi⟩ := (hY C).mp hC
    exact ⟨i, hQ.input_mem_of_pairMember hi, hi⟩)
  have merge {i j C D : M.Domain} (hi : M.PairMember I i C Q) (hj : M.PairMember I j D Q) :
      ∃ k E, M.PairMember I k E Q ∧ M.MemberSubset C E ∧ M.MemberSubset D E := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare i (hQ.input_mem_of_pairMember hi)
        j (hQ.input_mem_of_pairMember hj) with he | hij | hji
    · have he := hZF.1.eq_of_same_members i j he
      subst j
      have he := hQ.1.2 i D C hj hi
      subst D
      exact ⟨i, C, hi, fun _ h => h, fun _ h => h⟩
    · exact ⟨j, D, hj, increasing i j C D hij hi hj, fun _ h => h⟩
    · exact ⟨i, C, hi, fun _ h => h, increasing j i D C hji hj hi⟩
  obtain ⟨e, he, _⟩ := hω.1.1
  refine ⟨Q, N, ⟨hQ, hz, fun _ _ _ _ => succ⟩, hu,
    fun z hzA => (hu z).mpr ⟨e, A, hz e he, hzA⟩, ?_,
    ZFC.countable_union_l I hZFC hω hy hN (fun C hC => ?_), ?_⟩
  · intro z hzN
    obtain ⟨i, C, hi, hzC⟩ := (hu z).mp hzN
    exact (hP C).mp (hQ.output_mem_of_pairMember hi) z hzC
  · obtain ⟨i, hi⟩ := (hY C).mp hC
    exact count i (hQ.input_mem_of_pairMember hi) C hi
  · intro x y Z hx hy hxy z hzZ
    obtain ⟨i, C, hi, hxC⟩ := (hu x).mp hx
    obtain ⟨j, D, hj, hyD⟩ := (hu y).mp hy
    obtain ⟨k, E, hk, hCE, hDE⟩ := merge hi hj
    obtain ⟨l, hlk, hlω⟩ := hω.1.2 k (hQ.input_mem_of_pairMember hk)
    obtain ⟨B, _, hl⟩ := hQ.2.2 l hlω
    exact (hu z).mpr ⟨l, B, hl,
      (succ hlk hk hl z).mpr (Or.inr ⟨x, y, Z, hCE x hxC, hDE y hyD, hxy, hzZ⟩)⟩

def result {n : Nat} (𝒞 : OrderedPairConvention) (ω X P F A Q N : Term n) : Formula 1 n :=
  .conj (stages 𝒞 ω P F A Q) (.conj (cc_union_m 𝒞 Q N)
    (.conj (Formula.subset A N) (.conj (Formula.subset N X)
      (.conj (Formula.cardinalLessOrEqual 𝒞 N ω) (closed 𝒞 F N)))))
derive_free_closed result

theorem result_semantics (hE : Extensional M) {n : Nat} (ρ : Env M n)
    (ω X P F A Q N : Term n) :
    Formula.satisfies ρ (result 𝒞 ω X P F A Q N) ↔
      Stages I (ω.eval ρ) (P.eval ρ) (F.eval ρ) (A.eval ρ) (Q.eval ρ) ∧
      Cc_union_d I (Q.eval ρ) (N.eval ρ) ∧
      M.MemberSubset (A.eval ρ) (N.eval ρ) ∧ M.MemberSubset (N.eval ρ) (X.eval ρ) ∧
      M.CardinalLessOrEqual I (N.eval ρ) (ω.eval ρ) ∧ Closed I (F.eval ρ) (N.eval ρ) := by
  simp only [result, Formula.satisfies_conj_iff, stages_semantics I hE, cc_union_sat_l I,
    Formula.satisfies_subset_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE, closed_semantics I]
  rfl

end Internal

open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def rowsCountable {n : Nat} (ω F : Project.Term n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest F.weaken.weaken)
    (Formula.cardinalLessOrEqual PureKuratowskiProject.convention .newest ω.weaken.weaken)))
derive_free_closed rowsCountable

theorem rowsCountable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) n) (ω F : Project.Term n) :
    Formula.satisfies ρ (rowsCountable ω F) ↔
      ∀ q Y, (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) q Y (F.eval ρ) →
        (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual
          (KuratowskiZF.interpretation hM) Y (ω.eval ρ) := by
  simp only [rowsCountable, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Definitional.Term.eval_weaken]
  rfl

/-- Parameters: internal omega, ambient set, its square, powerset, given operation, seed. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6
    (.imp (Formula.isOmega (.bound 0))
      (.imp (Formula.isCartesianProduct PureKuratowskiProject.convention (.bound 2) (.bound 1) (.bound 1))
        (.imp (Formula.isPowerSet (.bound 3) (.bound 1))
          (.imp (Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound 4) (.bound 2) (.bound 3))
            (.imp (rowsCountable (.bound 0) (.bound 4))
              (.imp (Formula.subset (.bound 5) (.bound 1))
                (.imp (Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound 5) (.bound 0))
                  (.existsE (.existsE (result PureKuratowskiProject.convention
                    (.bound 2) (.bound 3) (.bound 5) (.bound 6) (.bound 7) (.bound 1) .newest))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, Formula.isOmega,
      Formula.isCartesianProduct_freeClosed, Formula.isPowerSet_freeClosed,
      Formula.isFunctionFromTo_freeClosed, rowsCountable_freeClosed,
      Formula.cardinalLessOrEqual_freeClosed, result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),
    Formula.satisfies_isPowerSet_iff,
    Formula.satisfies_isFunctionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    rowsCountable_semantics hM, Formula.satisfies_subset_iff,
    Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    result_semantics (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM), Project.Term.eval_bound]
  exact fun hω hXX hP hF hval hA ha => exists_hull (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) hω hXX hP hF hval hA ha

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionCountableHull
