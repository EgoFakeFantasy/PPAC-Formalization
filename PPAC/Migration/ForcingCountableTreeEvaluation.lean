/- Internal set-valued evaluation needed by pinned
AssignedGraphs.CountableHull.evaluate:289-292 and exists_closed:296-324.
Adapt the donor Borel.Boolean partial-solution agreement/merge/extension proof.
Every partial evaluation is an internal subset of T x X. Internal minimal
subsets suffice; no host WellFounded, ordinal standardness or Choice is used. -/
import PPAC.Migration.ForcingChainBound

namespace PPAC.Migration.ForcingCountableTreeEvaluation
open YesMetaZFC SetTheory SetTheory.Definitional.Project
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- Internal minimal-subset definition, as in donor wf_rel_ind_l. -/
def WellFounded (T R : M.Domain) : Prop :=
  ∀ Y, M.MemberSubset Y T → (∃ a, M.mem a Y) →
    ∃ a, M.mem a Y ∧ ∀ b, M.mem b Y → ¬ M.PairMember I b a R

def wellFounded {n} (T R : Term n) : Formula 1 n :=
  .forallE (.imp (Formula.subset .newest T.weaken) (.imp (.existsE (.mem .newest (.bound 1)))
    (Formula.existsMem .newest (Formula.forallMem (.bound 1)
      (.neg (Formula.orderedPairMem 𝒞 .newest (.bound 1) R.weaken.weaken.weaken))))))
derive_free_closed wellFounded

theorem wellFounded_semantics {n} (ρ : Env M n) (T R : Term n) :
    Formula.satisfies ρ (wellFounded (𝒞 := 𝒞) T R) ↔ WellFounded I (T.eval ρ) (R.eval ρ) := by
  simp only [wellFounded, WellFounded, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- Donor wf_rel_ind_l, with its pair convention made explicit. -/
theorem internal_induction (hZF : M.Models ZF) {T R} (hw : WellFounded I T R) {n}
    (φ : UnarySchema n) (ρ : Env M n)
    (h : ∀ a, M.mem a T → (∀ b, M.mem b T → M.PairMember I b a R → φ.denote ρ b) → φ.denote ρ a) :
    ∀ a, M.mem a T → φ.denote ρ a := by
  classical
  obtain ⟨Y, hY⟩ := ZF.separation_exists_d hZF φ.neg ρ T
  have hy a : M.mem a Y ↔ M.mem a T ∧ ¬ φ.denote ρ a := by
    simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hY a
  intro a ha
  apply Classical.byContradiction
  intro hn
  obtain ⟨b, hb, hm⟩ := hw Y (fun c hc => ((hy c).mp hc).1) ⟨a, (hy a).mpr ⟨ha, hn⟩⟩
  exact ((hy b).mp hb).2 (h b ((hy b).mp hb).1 (fun c hc hcb =>
    Classical.byContradiction (fun hn => hm c ((hy c).mpr ⟨hc, hn⟩) hcb)))

def Bounded (T X F : M.Domain) : Prop := M.IsSetFunction I F ∧
  ∀ a x, M.PairMember I a x F → M.mem a T ∧ M.mem x X

def Covered (T R F a : M.Domain) : Prop :=
  ∀ b, M.mem b T → M.PairMember I b a R → ∃ x, M.PairMember I b x F

def Agree (T R F G a : M.Domain) : Prop :=
  ∀ b, M.mem b T → M.PairMember I b a R → ∀ x, M.PairMember I b x F ↔ M.PairMember I b x G

def Partial (T R X O F : M.Domain) : Prop := Bounded I T X F ∧
  ∀ a x, M.PairMember I a x F → Covered I T R F a ∧ ForcingChainBound.Values I O F a x

def bounded {n} (T X F : Term n) : Formula 1 n :=
  .conj (Formula.isFunction 𝒞 F) (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (.conj (.mem (.bound 1) T.weaken.weaken) (.mem .newest X.weaken.weaken)))))
derive_free_closed bounded

def covered {n} (T R F a : Term n) : Formula 1 n :=
  Formula.forallMem T (.imp (Formula.orderedPairMem 𝒞 .newest a.weaken R.weaken)
    (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)))
derive_free_closed covered

def agree {n} (T R F G a : Term n) : Formula 1 n :=
  Formula.forallMem T (.imp (Formula.orderedPairMem 𝒞 .newest a.weaken R.weaken)
    (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken))))
derive_free_closed agree

def partialEval {n} (T R X O F : Term n) : Formula 1 n :=
  .conj (bounded (𝒞 := 𝒞) T X F) (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (.conj (covered (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken F.weaken.weaken (.bound 1))
        (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken F.weaken.weaken (.bound 1) .newest)))))
derive_free_closed partialEval

theorem bounded_semantics (hE : Extensional M) {n} (ρ : Env M n) (T X F : Term n) :
    Formula.satisfies ρ (bounded (𝒞 := 𝒞) T X F) ↔ Bounded I (T.eval ρ) (X.eval ρ) (F.eval ρ) := by
  simp only [bounded, Bounded, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem covered_semantics {n} (ρ : Env M n) (T R F a : Term n) :
    Formula.satisfies ρ (covered (𝒞 := 𝒞) T R F a) ↔
      Covered I (T.eval ρ) (R.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [covered, Covered, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem agree_semantics {n} (ρ : Env M n) (T R F G a : Term n) :
    Formula.satisfies ρ (agree (𝒞 := 𝒞) T R F G a) ↔
      Agree I (T.eval ρ) (R.eval ρ) (F.eval ρ) (G.eval ρ) (a.eval ρ) := by
  simp only [agree, Agree, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem partial_semantics (hE : Extensional M) {n} (ρ : Env M n) (T R X O F : Term n) :
    Formula.satisfies ρ (partialEval (𝒞 := 𝒞) T R X O F) ↔
      Partial I (T.eval ρ) (R.eval ρ) (X.eval ρ) (O.eval ρ) (F.eval ρ) := by
  simp only [partialEval, Partial, bounded_semantics I hE, covered_semantics I, ForcingChainBound.rel_semantics I,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- Source local evaluation reads only predecessor values. -/
def Local (T R X O : M.Domain) : Prop :=
  ∀ F G a, Bounded I T X F → Bounded I T X G → M.mem a T → Agree I T R F G a →
    ∀ x, ForcingChainBound.Values I O F a x ↔ ForcingChainBound.Values I O G a x

def Total (T R X O : M.Domain) : Prop :=
  ∀ F a, Bounded I T X F → M.mem a T → Covered I T R F a →
    ∃ x, M.mem x X ∧ ForcingChainBound.Values I O F a x

def Single (O : M.Domain) : Prop :=
  ∀ F a x y, ForcingChainBound.Values I O F a x → ForcingChainBound.Values I O F a y → x = y

/-- Retained donor agreement argument, now for internal set-valued graphs. -/
theorem partial_agree (hZF : M.Models ZF) {T R X O F G : M.Domain}
    (hw : WellFounded I T R) (hl : Local I T R X O) (hu : Single I O)
    (hF : Partial I T R X O F) (hG : Partial I T R X O G) :
    ∀ a x y, M.PairMember I a x F → M.PairMember I a y G → x = y := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push G
  let φ : UnarySchema 2 := {body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
      (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
      (Formula.extensionalEq (.bound 1) .newest))))}
  have hφ a : φ.denote ρ a ↔ ∀ x y, M.PairMember I a x F → M.PairMember I a y G → x = y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hall := internal_induction I hZF hw φ ρ (fun a ha ih => (hφ a).mpr (by
    intro x y hx hy
    have hagree : Agree I T R F G a := by
      intro b hb hba z
      obtain ⟨v, hv⟩ := (hF.2 a x hx).1 b hb hba
      obtain ⟨w, hw⟩ := (hG.2 a y hy).1 b hb hba
      have e := (hφ b).mp (ih b hb hba) v w hv hw
      subst w
      exact ⟨fun hz => hF.1.1.2 b z v hz hv ▸ hw,
        fun hz => hG.1.1.2 b z v hz hw ▸ hv⟩
    exact hu F a x y (hF.2 a x hx).2
      ((hl F G a hF.1 hG.1 ha hagree y).mpr (hG.2 a y hy).2)))
  intro a x y hx hy
  exact (hφ a).mp (hall a (hF.1.2 a x hx).1) x y hx hy

/-- Extend the SAME partial graph by one row, using the native insert set. -/
theorem partial_extend (hZF : M.Models ZF) {T R X O F a : M.Domain}
    (hl : Local I T R X O) (ht : Total I T R X O) (hF : Partial I T R X O F)
    (ha : M.mem a T) (hn : ¬ ∃ x, M.PairMember I a x F) (hcover : Covered I T R F a) :
    ∃ G x, Partial I T R X O G ∧ M.PairMember I a x G := by
  obtain ⟨x, hx, hstep⟩ := ht F a hF.1 ha hcover
  obtain ⟨p, hp⟩ := I.total a x
  obtain ⟨G, hG⟩ := KP.exists_insert (ZF.modelsKP hZF) F p
  have edge b y : M.PairMember I b y G ↔ M.PairMember I b y F ∨ (b = a ∧ y = x) := by
    constructor
    · rintro ⟨q, hq, hqG⟩
      rcases (hG q).mp hqG with hqF | rfl
      · exact Or.inl ⟨q, hq, hqF⟩
      · exact Or.inr (I.injective hq hp)
    · rintro (hb | ⟨rfl, rfl⟩)
      · obtain ⟨q, hq, hqF⟩ := hb
        exact ⟨q, hq, (hG q).mpr (Or.inl hqF)⟩
      · exact ⟨p, hp, (hG p).mpr (Or.inr rfl)⟩
  have boundedG : Bounded I T X G := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro q hq
      rcases (hG q).mp hq with hq | rfl
      · exact hF.1.1.1 q hq
      · exact ⟨a, x, hp⟩
    · intro b y z hy hz
      rcases (edge b y).mp hy with hy | hy <;>
        rcases (edge b z).mp hz with hz | hz
      · exact hF.1.1.2 b y z hy hz
      · exact (hn ⟨y, hz.1 ▸ hy⟩).elim
      · exact (hn ⟨z, hy.1 ▸ hz⟩).elim
      · exact hy.2.trans hz.2.symm
    · intro b y hby
      rcases (edge b y).mp hby with hby | hby
      · exact hF.1.2 b y hby
      · exact ⟨hby.1.symm ▸ ha, hby.2.symm ▸ hx⟩
  have same b (hc : Covered I T R F b) : Agree I T R F G b := by
    intro c hcT hcb y
    constructor
    · exact fun h => (edge c y).mpr (Or.inl h)
    · intro h
      rcases (edge c y).mp h with h | h
      · exact h
      · obtain ⟨z, hz⟩ := hc c hcT hcb
        exact (hn ⟨z, h.1 ▸ hz⟩).elim
  refine ⟨G, x, ⟨boundedG, ?_⟩, (edge a x).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  intro b y hby
  rcases (edge b y).mp hby with hby | ⟨eb, ey⟩
  · have hc := (hF.2 b y hby).1
    refine ⟨fun c hcT hcb => ?_, (hl F G b hF.1 boundedG (hF.1.2 b y hby).1 (same b hc) y).mp (hF.2 b y hby).2⟩
    obtain ⟨z, hz⟩ := hc c hcT hcb
    exact ⟨z, (edge c z).mpr (Or.inl hz)⟩
  · subst b
    subst y
    refine ⟨fun c hcT hca => ?_, (hl F G a hF.1 boundedG ha (same a hcover) x).mp hstep⟩
    obtain ⟨z, hz⟩ := hcover c hcT hca
    exact ⟨z, (edge c z).mpr (Or.inl hz)⟩

/-- Merge all internal partial evaluations; internal induction proves totality.
This is the donor br_eval_exists_unique_l construction with set-valued rows. -/
theorem evaluation_exists (hZF : M.Models ZF) {T R X O : M.Domain}
    (hw : WellFounded I T R) (hl : Local I T R X O) (ht : Total I T R X O) (hu : Single I O) :
    ∃ G, M.IsSetFunctionFromTo I G T X ∧ Partial I T R X O G := by
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I T X
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF Q
  let ρ : Env M 4 := (((⟨fun _ => T, fun _ => T⟩ : Env M 1).push R).push X).push O
  let φ : UnarySchema 4 := {body := partialEval (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest}
  have hφ F : φ.denote ρ F ↔ Partial I T R X O F := by
    simp only [φ, UnarySchema.denote, partial_semantics I hZF.1]
    rfl
  obtain ⟨A, hA'⟩ := ZF.separation_exists_d hZF φ ρ K
  have hA F : M.mem F A ↔ Partial I T R X O F := by
    rw [hA' F]
    change (M.mem F K ∧ φ.denote ρ F) ↔ _
    rw [hφ F]
    refine ⟨And.right, fun hF => ⟨(hK F).mpr ?_, hF⟩⟩
    intro q hq
    obtain ⟨a, x, hax⟩ := hF.1.1.1 q hq
    have hb := hF.1.2 a x ⟨q, hax, hq⟩
    exact (hQ q).mpr ⟨a, hb.1, x, hb.2, hax⟩
  obtain ⟨G, hG⟩ := KP.exists_union (ZF.modelsKP hZF) A
  have edge a x : M.PairMember I a x G ↔ ∃ F, Partial I T R X O F ∧ M.PairMember I a x F := by
    constructor
    · rintro ⟨p, hp, hpG⟩
      obtain ⟨F, hF, hpF⟩ := (hG p).mp hpG
      exact ⟨F, (hA F).mp hF, p, hp, hpF⟩
    · rintro ⟨F, hF, p, hp, hpF⟩
      exact ⟨p, hp, (hG p).mpr ⟨F, (hA F).mpr hF, hpF⟩⟩
  have boundedG : Bounded I T X G := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨F, hF, hpF⟩ := (hG p).mp hp
      exact ((hA F).mp hF).1.1.1 p hpF
    · intro a x y hx hy
      obtain ⟨F, hF, hx⟩ := (edge a x).mp hx
      obtain ⟨H, hH, hy⟩ := (edge a y).mp hy
      exact partial_agree I hZF hw hl hu hF hH a x y hx hy
    · intro a x hx
      obtain ⟨F, hF, hx⟩ := (edge a x).mp hx
      exact hF.1.2 a x hx
  have goodG : Partial I T R X O G := by
    refine ⟨boundedG, ?_⟩
    intro a x hx
    obtain ⟨F, hF, hx⟩ := (edge a x).mp hx
    have same : Agree I T R F G a := by
      intro b hb hba y
      constructor
      · exact fun hy => (edge b y).mpr ⟨F, hF, hy⟩
      · intro hy
        obtain ⟨v, hv⟩ := (hF.2 a x hx).1 b hb hba
        obtain ⟨H, hH, hy⟩ := (edge b y).mp hy
        exact partial_agree I hZF hw hl hu hH hF b y v hy hv ▸ hv
    refine ⟨fun b hb hba => ?_, (hl F G a hF.1 boundedG (hF.1.2 a x hx).1 same x).mp (hF.2 a x hx).2⟩
    obtain ⟨y, hy⟩ := (hF.2 a x hx).1 b hb hba
    exact ⟨y, (edge b y).mpr ⟨F, hF, hy⟩⟩
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : UnarySchema 1 := {body := .existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))}
  have hψ a : ψ.denote η a ↔ ∃ x, M.PairMember I a x G := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  have all := internal_induction I hZF hw ψ η (fun a ha ih => (hψ a).mpr (by
    classical
    by_cases hn : ∃ x, M.PairMember I a x G
    · exact hn
    · obtain ⟨F, x, hF, hx⟩ := partial_extend I hZF hl ht goodG ha hn (fun b hb hba => (hψ b).mp (ih b hb hba))
      exact ⟨x, (edge a x).mpr ⟨F, hF, hx⟩⟩))
  have full a (ha : M.mem a T) := (hψ a).mp (all a ha)
  refine ⟨G, ⟨boundedG.1, ?_, ?_⟩, goodG⟩
  · intro a
    exact ⟨fun ha => full a ha, fun ⟨x, hx⟩ => (boundedG.2 a x hx).1⟩
  · intro a ha
    obtain ⟨x, hx⟩ := full a ha
    exact ⟨x, (boundedG.2 a x hx).2, hx⟩

theorem evaluation_unique (hZF : M.Models ZF) {T R X O F G : M.Domain}
    (hw : WellFounded I T R) (hl : Local I T R X O) (hu : Single I O)
    (hf : M.IsSetFunctionFromTo I F T X) (hg : M.IsSetFunctionFromTo I G T X)
    (hF : Partial I T R X O F) (hG : Partial I T R X O G) : F = G := by
  have eqv a x : M.PairMember I a x F ↔ M.PairMember I a x G := by
    constructor
    · intro hx
      obtain ⟨y, _, hy⟩ := hg.2.2 a (hf.input_mem_of_pairMember hx)
      exact (partial_agree I hZF hw hl hu hF hG a x y hx hy).symm ▸ hy
    · intro hx
      obtain ⟨y, _, hy⟩ := hf.2.2 a (hg.input_mem_of_pairMember hx)
      exact (partial_agree I hZF hw hl hu hG hF a x y hx hy).symm ▸ hy
  apply hZF.1.eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨a, x, hc⟩ := hf.1.1 p hp
    obtain ⟨q, hq, hqG⟩ := (eqv a x).mp ⟨p, hc, hp⟩
    exact (I.unique hc hq).symm ▸ hqG
  · intro hp
    obtain ⟨a, x, hc⟩ := hg.1.1 p hp
    obtain ⟨q, hq, hqF⟩ := (eqv a x).mpr ⟨p, hc, hp⟩
    exact (I.unique hc hq).symm ▸ hqF

def localOperator {n} (T R X O : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp
    (bounded (𝒞 := 𝒞) T.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 2)) (.imp
      (bounded (𝒞 := 𝒞) T.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 1)) (.imp
        (.mem .newest T.weaken.weaken.weaken) (.imp
          (agree (𝒞 := 𝒞) T.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
          (.forallE (.iff
            (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
            (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))))))
derive_free_closed localOperator

def totalOperator {n} (T R X O : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (bounded (𝒞 := 𝒞) T.weaken.weaken X.weaken.weaken (.bound 1))
    (.imp (.mem .newest T.weaken.weaken)
      (.imp (covered (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken (.bound 1) .newest)
        (.existsE (.conj (.mem .newest X.weaken.weaken.weaken)
          (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))))
derive_free_closed totalOperator

def singleOperator {n} (O : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.imp
    (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
      (.imp (ForcingChainBound.rel (𝒞 := 𝒞) O.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)
        (Formula.extensionalEq (.bound 1) .newest))))))
derive_free_closed singleOperator

def evaluation {n} (T R X O F : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 F T X) (partialEval (𝒞 := 𝒞) T R X O F)
derive_free_closed evaluation

theorem localOperator_semantics (hE : Extensional M) {n} (ρ : Env M n) (T R X O : Term n) :
    Formula.satisfies ρ (localOperator (𝒞 := 𝒞) T R X O) ↔
      Local I (T.eval ρ) (R.eval ρ) (X.eval ρ) (O.eval ρ) := by
  simp only [localOperator, Local, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, bounded_semantics I hE,
    agree_semantics I, ForcingChainBound.rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem totalOperator_semantics (hE : Extensional M) {n} (ρ : Env M n) (T R X O : Term n) :
    Formula.satisfies ρ (totalOperator (𝒞 := 𝒞) T R X O) ↔
      Total I (T.eval ρ) (R.eval ρ) (X.eval ρ) (O.eval ρ) := by
  simp only [totalOperator, Total, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    bounded_semantics I hE, covered_semantics I, ForcingChainBound.rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem singleOperator_semantics (hE : Extensional M) {n} (ρ : Env M n) (O : Term n) :
    Formula.satisfies ρ (singleOperator (𝒞 := 𝒞) O) ↔ Single I (O.eval ρ) := by
  simp only [singleOperator, Single, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, ForcingChainBound.rel_semantics I,
    Definitional.Term.eval_weaken]
  rfl

theorem evaluation_semantics (hE : Extensional M) {n} (ρ : Env M n) (T R X O F : Term n) :
    Formula.satisfies ρ (evaluation (𝒞 := 𝒞) T R X O F) ↔
      M.IsSetFunctionFromTo I (F.eval ρ) (T.eval ρ) (X.eval ρ) ∧
        Partial I (T.eval ρ) (R.eval ρ) (X.eval ρ) (O.eval ρ) (F.eval ρ) := by
  simp only [evaluation, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    partial_semantics I hE]

/-- All internal relation/node/value/operator sets; unique total evaluation. -/
def evaluationSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 4
    (.imp (wellFounded (𝒞 := 𝒞) (.bound 0) (.bound 1))
      (.imp (localOperator (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3))
        (.imp (totalOperator (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3))
          (.imp (singleOperator (𝒞 := 𝒞) (.bound 3))
            (.existsE (.conj (evaluation (𝒞 := 𝒞) (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest)
              (.forallE (.imp (evaluation (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest)
                (Formula.extensionalEq .newest (.bound 1))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
/-- Same universe, arbitrary possibly externally ill-founded models. -/
theorem evaluation_models (hZF : M.Models ZF) : M.SatisfiesSentence (evaluationSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    wellFounded_semantics I, localOperator_semantics I hZF.1, totalOperator_semantics I hZF.1,
    singleOperator_semantics I hZF.1, evaluation_semantics I hZF.1]
  intro hw hl ht hu
  obtain ⟨F, hf, hF⟩ := evaluation_exists I hZF hw hl ht hu
  exact ⟨F, ⟨hf, hF⟩, fun G hG => evaluation_unique I hZF hw hl hu hG.1 hf hG.2 hF⟩

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

/-- Ordinary nativeZF original-kernel certificate, with no object Choice. -/
theorem evaluation_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (evaluationSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (evaluation_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeEvaluation
