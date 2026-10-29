/- Pinned AssignedGraphs.CountableHull.evaluate:289-292.
Leaf nodes evaluate to base; each other node applies the given label operation
to the INTERNAL function of all child values. Discharge Local/Total/Single
of the retained internal evaluator using native function graph construction. -/
import PPAC.Migration.ForcingCountableTreeEvaluation

namespace PPAC.Migration.ForcingCountableTreeAlgebra
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ForcingChainBound (Values rel rel_semantics)
open ForcingCountableTreeEvaluation (Bounded Covered Agree WellFounded)
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- The source some-label at each non-leaf; leaves are the none case. -/
def Labels (T A L labels : M.Domain) : Prop := M.IsSetFunction I labels ∧
  (∀ a l, M.PairMember I a l labels → M.mem a T ∧ ¬ M.mem a L ∧ M.mem l A) ∧
  ∀ a, M.mem a T → ¬ M.mem a L → ∃ l, M.PairMember I a l labels

/-- The complete internal child function at each non-leaf, indexed by w. -/
def Children (T R w L children : M.Domain) : Prop :=
  ∀ a, M.mem a T → ¬ M.mem a L → ∀ n, M.mem n w →
    (∃ b, Values I children a n b) ∧
    (∀ b, Values I children a n b → M.mem b T ∧ M.PairMember I b a R) ∧
    ∀ b c, Values I children a n b → Values I children a n c → b = c

def Operation (w A X op : M.Domain) : Prop :=
  (∀ l, M.mem l A → ∀ g, M.IsSetFunctionFromTo I g w X → ∃ x, M.mem x X ∧ Values I op l g x) ∧
  ∀ l g x y, Values I op l g x → Values I op l g y → x = y

/-- Exact child-value graph, with no external choice of a sequence. -/
def Arguments (w X children F a g : M.Domain) : Prop := M.IsSetFunctionFromTo I g w X ∧
  ∀ n y, M.PairMember I n y g ↔ M.mem n w ∧ ∃ b, Values I children a n b ∧ M.PairMember I b y F

def arguments {n} (w X children F a g : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 g w X) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
    (.conj (.mem (.bound 1) w.weaken.weaken) (.existsE (.conj
      (rel (𝒞 := 𝒞) children.weaken.weaken.weaken a.weaken.weaken.weaken (.bound 2) .newest)
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) F.weaken.weaken.weaken)))))))
derive_free_closed arguments

theorem arguments_semantics (hE : Extensional M) {n} (ρ : Env M n) (w X children F a g : Term n) :
    Formula.satisfies ρ (arguments (𝒞 := 𝒞) w X children F a g) ↔
      Arguments I (w.eval ρ) (X.eval ρ) (children.eval ρ) (F.eval ρ) (a.eval ρ) (g.eval ρ) := by
  simp only [arguments, Arguments, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem arguments_exists (hZF : M.Models ZF) {T R w X L children F a : M.Domain}
    (hc : Children I T R w L children) (hf : Bounded I T X F)
    (ha : M.mem a T) (hn : ¬ M.mem a L) (hcover : Covered I T R F a) :
    ∃ g, Arguments I w X children F a g := by
  let ρ : Env M 3 := ((⟨fun _ => children, fun _ => children⟩ : Env M 1).push a).push F
  let φ : BinarySchema 3 := {body := .existsE (.conj
    (rel (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 2) .newest)
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3)))}
  have hφ n y : φ.denote ρ n y ↔ ∃ b, Values I children a n b ∧ M.PairMember I b y F := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rel_semantics I, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨g, hg, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := w) (target := X) (by
    intro n hnw
    obtain ⟨b, hb⟩ := (hc a ha hn n hnw).1
    have hbT := (hc a ha hn n hnw).2.1 b hb
    obtain ⟨y, hy⟩ := hcover b hbT.1 hbT.2
    exact ⟨y, (hφ n y).mpr ⟨b, hb, hy⟩⟩) (by
    intro n hnw y z hy hz
    obtain ⟨b, hb, hy⟩ := (hφ n y).mp hy
    obtain ⟨c, hcc, hz⟩ := (hφ n z).mp hz
    have e := (hc a ha hn n hnw).2.2 b c hb hcc
    subst c
    exact hf.1.2 b y z hy hz) (by
    intro n y _ hy
    obtain ⟨b, _, hby⟩ := (hφ n y).mp hy
    exact (hf.2 b y hby).2)
  exact ⟨g, hg, fun n y => (he n y).trans (and_congr_right fun _ => hφ n y)⟩

theorem arguments_unique (hE : Extensional M) {w X children F a g h : M.Domain}
    (hg : Arguments I w X children F a g) (hh : Arguments I w X children F a h) : g = h := by
  have eqv n y := (hg.2 n y).trans (hh.2 n y).symm
  apply hE.eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨n, y, hc⟩ := hg.1.1.1 p hp
    obtain ⟨q, hq, hqh⟩ := (eqv n y).mp ⟨p, hc, hp⟩
    exact (I.unique hc hq).symm ▸ hqh
  · intro hp
    obtain ⟨n, y, hc⟩ := hh.1.1.1 p hp
    obtain ⟨q, hq, hqg⟩ := (eqv n y).mpr ⟨p, hc, hp⟩
    exact (I.unique hc hq).symm ▸ hqg

theorem arguments_congr {T R w X L children F G a g : M.Domain}
    (hc : Children I T R w L children) (ha : M.mem a T) (hn : ¬ M.mem a L)
    (hsame : Agree I T R F G a) :
    Arguments I w X children F a g ↔ Arguments I w X children G a g := by
  have eqv n (hnw : M.mem n w) y :
      (∃ b, Values I children a n b ∧ M.PairMember I b y F) ↔
        ∃ b, Values I children a n b ∧ M.PairMember I b y G := by
    apply exists_congr
    intro b
    apply and_congr_right
    intro hb
    have ht := (hc a ha hn n hnw).2.1 b hb
    exact hsame b ht.1 ht.2 y
  exact and_congr_right (fun _ => forall_congr' fun n => forall_congr' fun y =>
    iff_congr Iff.rfl (and_congr_right fun hnw => eqv n hnw y))

def Step (w T X L labels children op base F a x : M.Domain) : Prop :=
  Bounded I T X F ∧ M.mem a T ∧ M.mem x X ∧
    ((M.mem a L ∧ x = base) ∨ (¬ M.mem a L ∧ ∃ l g,
      M.PairMember I a l labels ∧ Arguments I w X children F a g ∧ Values I op l g x))

def step {n} (w T X L labels children op base F a x : Term n) : Formula 1 n :=
  .conj (ForcingCountableTreeEvaluation.bounded (𝒞 := 𝒞) T X F)
    (.conj (.mem a T) (.conj (.mem x X) (.disj
      (.conj (.mem a L) (Formula.extensionalEq x base))
      (.conj (.neg (.mem a L)) (.existsE (.existsE (.conj
        (Formula.orderedPairMem 𝒞 a.weaken.weaken (.bound 1) labels.weaken.weaken)
        (.conj (arguments (𝒞 := 𝒞) w.weaken.weaken X.weaken.weaken children.weaken.weaken F.weaken.weaken a.weaken.weaken .newest)
          (rel (𝒞 := 𝒞) op.weaken.weaken (.bound 1) .newest x.weaken.weaken)))))))))
derive_free_closed step

theorem step_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w T X L labels children op base F a x : Term n) :
    Formula.satisfies ρ (step (𝒞 := 𝒞) w T X L labels children op base F a x) ↔
      Step I (w.eval ρ) (T.eval ρ) (X.eval ρ) (L.eval ρ) (labels.eval ρ) (children.eval ρ)
        (op.eval ρ) (base.eval ρ) (F.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [step, Step, ForcingCountableTreeEvaluation.bounded_semantics I hE,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_extensionalEq_iff_eq hE, arguments_semantics I hE, rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem step_local {T R w X L labels children op base F G a x : M.Domain}
    (hc : Children I T R w L children) (hf : Bounded I T X F) (hg : Bounded I T X G)
    (ha : M.mem a T) (hsame : Agree I T R F G a) :
    Step I w T X L labels children op base F a x ↔ Step I w T X L labels children op base G a x := by
  have cores : ((M.mem a L ∧ x = base) ∨ (¬ M.mem a L ∧ ∃ l g,
      M.PairMember I a l labels ∧ Arguments I w X children F a g ∧ Values I op l g x)) ↔
      ((M.mem a L ∧ x = base) ∨ (¬ M.mem a L ∧ ∃ l g,
      M.PairMember I a l labels ∧ Arguments I w X children G a g ∧ Values I op l g x)) := by
    apply or_congr Iff.rfl
    apply and_congr_right
    intro hn
    apply exists_congr
    intro l
    apply exists_congr
    intro g
    exact and_congr_right (fun _ => and_congr (arguments_congr I hc ha hn hsame) Iff.rfl)
  exact ⟨fun h => ⟨hg, h.2.1, h.2.2.1, cores.mp h.2.2.2⟩,
    fun h => ⟨hf, h.2.1, h.2.2.1, cores.mpr h.2.2.2⟩⟩

theorem step_total (hZF : M.Models ZF) {T R w A X L labels children op base F a : M.Domain}
    (hl : Labels I T A L labels) (hc : Children I T R w L children)
    (ho : Operation I w A X op) (hb : M.mem base X) (hf : Bounded I T X F)
    (ha : M.mem a T) (hcover : Covered I T R F a) :
    ∃ x, M.mem x X ∧ Step I w T X L labels children op base F a x := by
  classical
  by_cases hn : M.mem a L
  · exact ⟨base, hb, hf, ha, hb, Or.inl ⟨hn, rfl⟩⟩
  · obtain ⟨l, hal⟩ := hl.2.2 a ha hn
    obtain ⟨g, hg⟩ := arguments_exists I hZF hc hf ha hn hcover
    obtain ⟨x, hx, hox⟩ := ho.1 l (hl.2.1 a l hal).2.2 g hg.1
    exact ⟨x, hx, hf, ha, hx, Or.inr ⟨hn, l, g, hal, hg, hox⟩⟩

theorem step_unique (hE : Extensional M) {T w A X L labels children op base F a x y : M.Domain}
    (hl : Labels I T A L labels) (ho : Operation I w A X op)
    (hx : Step I w T X L labels children op base F a x)
    (hy : Step I w T X L labels children op base F a y) : x = y := by
  rcases hx.2.2.2 with ⟨hxL, hxb⟩ | ⟨hxL, l, g, hal, hg, hox⟩ <;>
    rcases hy.2.2.2 with ⟨hyL, hyb⟩ | ⟨hyL, m, h, ham, hh, hoy⟩
  · exact hxb.trans hyb.symm
  · exact (hyL hxL).elim
  · exact (hxL hyL).elim
  · have e := hl.1.2 a l m hal ham
    subst m
    have e := arguments_unique I hE hg hh
    subst h
    exact ho.2 l g x y hox hoy

/-- The real leaf/node step is represented by an internal ternary graph.
Only Separation on P(T x X) x (T x X) is needed. -/
theorem operator_exists (hZF : M.Models ZF) (w T X L labels children op base : M.Domain) :
    ∃ O, ∀ F a x, Values I O F a x ↔ Step I w T X L labels children op base F a x := by
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I T X
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF Q
  obtain ⟨Z, hZ⟩ := ZF.exists_cartesianProduct hZF I K Q
  let ρ : Env M 8 := (((((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push T).push X).push L).push labels).push children).push op).push base
  let φ : UnarySchema 8 := {body := .existsE (.existsE (.existsE (.existsE (.conj
    (𝒞.code (.bound 4) (.bound 3) .newest) (.conj
      (𝒞.code .newest (.bound 2) (.bound 1))
      (step (𝒞 := 𝒞) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1)))))))}
  have hφ z : φ.denote ρ z ↔ ∃ F a x ax, I.Codes z F ax ∧ I.Codes ax a x ∧
      Step I w T X L labels children op base F a x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, step_semantics I hZF.1]
    rfl
  obtain ⟨O, hO⟩ := ZF.separation_exists_d hZF φ ρ Z
  refine ⟨O, fun F a x => ?_⟩
  constructor
  · rintro ⟨ax, hax, z, hz, hzO⟩
    obtain ⟨F', a', x', ax', hz', hax', hs⟩ := (hφ z).mp ((hO z).mp hzO).2
    obtain ⟨rfl, rfl⟩ := I.injective hz hz'
    obtain ⟨rfl, rfl⟩ := I.injective hax hax'
    exact hs
  · intro hs
    have hFK : M.mem F K := (hK F).mpr (by
      intro z hz
      obtain ⟨b, y, hby⟩ := hs.1.1.1 z hz
      have hb := hs.1.2 b y ⟨z, hby, hz⟩
      exact (hQ z).mpr ⟨b, hb.1, y, hb.2, hby⟩)
    obtain ⟨ax, hax⟩ := I.total a x
    obtain ⟨z, hz⟩ := I.total F ax
    exact ⟨ax, hax, z, hz, (hO z).mpr ⟨(hZ z).mpr
      ⟨F, hFK, ax, (hQ ax).mpr ⟨a, hs.2.1, x, hs.2.2.1, hax⟩, hz⟩,
      (hφ z).mpr ⟨F, a, x, ax, hz, hax, hs⟩⟩⟩

def Evaluation (w T X L labels children op base F : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I F T X ∧ ∀ a x, M.PairMember I a x F →
    Step I w T X L labels children op base F a x

/-- Source evaluate, with its leaf and all-child operation instantiated.
No Local/Total/Single premise remains for the evaluation operator itself. -/
theorem evaluate (hZF : M.Models ZF) {T R w A X L labels children op base : M.Domain}
    (hw : WellFounded I T R) (hl : Labels I T A L labels) (hc : Children I T R w L children)
    (ho : Operation I w A X op) (hb : M.mem base X) :
    ∃ F, Evaluation I w T X L labels children op base F ∧
      ∀ G, Evaluation I w T X L labels children op base G → G = F := by
  obtain ⟨O, hO⟩ := operator_exists I hZF w T X L labels children op base
  have hlocal : ForcingCountableTreeEvaluation.Local I T R X O := by
    intro F G a hf hg ha hsame x
    exact (hO F a x).trans ((step_local I hc hf hg ha hsame).trans (hO G a x).symm)
  have htotal : ForcingCountableTreeEvaluation.Total I T R X O := by
    intro F a hf ha hcover
    obtain ⟨x, hx, hs⟩ := step_total I hZF hl hc ho hb hf ha hcover
    exact ⟨x, hx, (hO F a x).mpr hs⟩
  have hsingle : ForcingCountableTreeEvaluation.Single I O := by
    intro F a x y hx hy
    exact step_unique I hZF.1 hl ho ((hO F a x).mp hx) ((hO F a y).mp hy)
  obtain ⟨F, hf, hF⟩ := ForcingCountableTreeEvaluation.evaluation_exists I hZF hw hlocal htotal hsingle
  refine ⟨F, ⟨hf, fun a x hx => (hO F a x).mp (hF.2 a x hx).2⟩, ?_⟩
  intro G hG
  have hg : ForcingCountableTreeEvaluation.Partial I T R X O G := by
    refine ⟨⟨hG.1.1, fun a x hx => ⟨hG.1.input_mem_of_pairMember hx, hG.1.output_mem_of_pairMember hx⟩⟩, ?_⟩
    intro a x hx
    refine ⟨fun b hb _ => ?_, (hO G a x).mpr (hG.2 a x hx)⟩
    obtain ⟨y, _, hy⟩ := hG.1.2.2 b hb
    exact ⟨y, hy⟩
  exact ForcingCountableTreeEvaluation.evaluation_unique I hZF hw hlocal hsingle hG.1 hf hg hF

def labelsFormula {n} (T A L labels : Term n) : Formula 1 n :=
  .conj (Formula.isFunction 𝒞 labels) (.conj
    (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest labels.weaken.weaken)
      (.conj (.mem (.bound 1) T.weaken.weaken) (.conj (.neg (.mem (.bound 1) L.weaken.weaken))
        (.mem .newest A.weaken.weaken))))))
    (Formula.forallMem T (.imp (.neg (.mem .newest L.weaken))
      (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest labels.weaken.weaken)))))
derive_free_closed labelsFormula

def childrenFormula {n} (T R w L children : Term n) : Formula 1 n :=
  Formula.forallMem T (.imp (.neg (.mem .newest L.weaken)) (Formula.forallMem w.weaken
    (.conj (.existsE (rel (𝒞 := 𝒞) children.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))
      (.conj (.forallE (.imp
        (rel (𝒞 := 𝒞) children.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.conj (.mem .newest T.weaken.weaken.weaken)
          (Formula.orderedPairMem 𝒞 .newest (.bound 2) R.weaken.weaken.weaken))))
        (.forallE (.forallE (.imp
          (rel (𝒞 := 𝒞) children.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
          (.imp (rel (𝒞 := 𝒞) children.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)
            (Formula.extensionalEq (.bound 1) .newest)))))))))
derive_free_closed childrenFormula

def operationFormula {n} (w A X op : Term n) : Formula 1 n :=
  .conj (Formula.forallMem A (.forallE (.imp
    (Formula.isFunctionFromTo 𝒞 .newest w.weaken.weaken X.weaken.weaken)
    (Formula.existsMem X.weaken.weaken
      (rel (𝒞 := 𝒞) op.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))
    (.forallE (.forallE (.forallE (.forallE (.imp
      (rel (𝒞 := 𝒞) op.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
        (.imp (rel (𝒞 := 𝒞) op.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)
          (Formula.extensionalEq (.bound 1) .newest)))))))
derive_free_closed operationFormula

def evaluation {n} (w T X L labels children op base F : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 F T X) (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (step (𝒞 := 𝒞) w.weaken.weaken T.weaken.weaken X.weaken.weaken L.weaken.weaken
        labels.weaken.weaken children.weaken.weaken op.weaken.weaken base.weaken.weaken
        F.weaken.weaken (.bound 1) .newest))))
derive_free_closed evaluation

theorem labels_semantics (hE : Extensional M) {n} (ρ : Env M n) (T A L labels : Term n) :
    Formula.satisfies ρ (labelsFormula (𝒞 := 𝒞) T A L labels) ↔
      Labels I (T.eval ρ) (A.eval ρ) (L.eval ρ) (labels.eval ρ) := by
  simp only [labelsFormula, Labels, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem children_semantics (hE : Extensional M) {n} (ρ : Env M n) (T R w L children : Term n) :
    Formula.satisfies ρ (childrenFormula (𝒞 := 𝒞) T R w L children) ↔
      Children I (T.eval ρ) (R.eval ρ) (w.eval ρ) (L.eval ρ) (children.eval ρ) := by
  simp only [childrenFormula, Children, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_extensionalEq_iff_eq hE, rel_semantics I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem operation_semantics (hE : Extensional M) {n} (ρ : Env M n) (w A X op : Term n) :
    Formula.satisfies ρ (operationFormula (𝒞 := 𝒞) w A X op) ↔
      Operation I (w.eval ρ) (A.eval ρ) (X.eval ρ) (op.eval ρ) := by
  simp only [operationFormula, Operation, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_extensionalEq_iff_eq hE,
    rel_semantics I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem evaluation_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w T X L labels children op base F : Term n) :
    Formula.satisfies ρ (evaluation (𝒞 := 𝒞) w T X L labels children op base F) ↔
      Evaluation I (w.eval ρ) (T.eval ρ) (X.eval ρ) (L.eval ρ) (labels.eval ρ)
        (children.eval ρ) (op.eval ρ) (base.eval ρ) (F.eval ρ) := by
  simp only [evaluation, Evaluation, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    step_semantics I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- Source leaf/node equations on all INTERNAL natural child indices. -/
def evaluationSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 10 (.imp (Formula.isOmega (.bound 0))
    (.imp (ForcingCountableTreeEvaluation.wellFounded (𝒞 := 𝒞) (.bound 1) (.bound 2))
      (.imp (labelsFormula (𝒞 := 𝒞) (.bound 1) (.bound 3) (.bound 5) (.bound 6))
        (.imp (childrenFormula (𝒞 := 𝒞) (.bound 1) (.bound 2) (.bound 0) (.bound 5) (.bound 7))
          (.imp (operationFormula (𝒞 := 𝒞) (.bound 0) (.bound 3) (.bound 4) (.bound 8))
            (.imp (.mem (.bound 9) (.bound 4))
              (.existsE (.conj (evaluation (𝒞 := 𝒞) (.bound 1) (.bound 2) (.bound 5) (.bound 6)
                (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest)
                (.forallE (.imp (evaluation (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 6) (.bound 7)
                  (.bound 8) (.bound 9) (.bound 10) (.bound 11) .newest)
                  (Formula.extensionalEq .newest (.bound 1))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
theorem evaluation_models (hZF : M.Models ZF) : M.SatisfiesSentence (evaluationSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    ForcingCountableTreeEvaluation.wellFounded_semantics I, labels_semantics I hZF.1,
    children_semantics I hZF.1, operation_semantics I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    evaluation_semantics I hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]
  exact fun _ hw hl hc ho hb => evaluate I hZF hw hl hc ho hb

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem evaluation_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (evaluationSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (evaluation_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeAlgebra
