/- Pinned AssignedGraphs.CountableHull.evaluate:289-292 on the ACTUAL
internal tree carrier. Build the leaf set and child graph, retaining every
internal child index, then consume the already proved evaluation operator. -/
import PPAC.Migration.ForcingCountableTreeCardinality

namespace PPAC.Migration.ForcingCountableTreeValues
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingTreeAddresses ForcingCountableTreeCodes
open ForcingChainBound (Values rel rel_semantics)
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Leaves (T labels L : M.Domain) : Prop := ∀ s,
  M.mem s L ↔ M.mem s T ∧ ¬ ∃ a, M.PairMember I s a labels

def leaves {n} (T labels L : Term n) : Formula 1 n := .forallE (.iff (.mem .newest L.weaken)
  (.conj (.mem .newest T.weaken) (.neg (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest labels.weaken.weaken)))))
derive_free_closed leaves

theorem leaves_semantics {n} (ρ : Env M n) (T labels L : Term n) :
    Formula.satisfies ρ (leaves (𝒞 := 𝒞) T labels L) ↔ Leaves I (T.eval ρ) (labels.eval ρ) (L.eval ρ) := by
  simp only [leaves, Leaves, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem leaves_exists (hZF : M.Models ZF) (T labels : M.Domain) : ∃ L, Leaves I T labels L := by
  let ρ : Env M 1 := ⟨fun _ => labels, fun _ => labels⟩
  let φ : UnarySchema 1 := {body := .neg (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)))}
  obtain ⟨L, hL⟩ := ZF.separation_exists_d hZF φ ρ T
  refine ⟨L, fun s => ?_⟩
  have hφ : φ.denote ρ s ↔ ¬ ∃ a, M.PairMember I s a labels := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  exact (hL s).trans (and_congr_right fun _ => hφ)

def ChildGraph (w T D : M.Domain) : Prop := ∀ s n t,
  Values I D s n t ↔ M.mem s T ∧ M.mem n w ∧ M.mem t T ∧ Fseq_end_d I w t s n

def childGraph {n} (w T D : Term n) : Formula 1 n := .forallE (.forallE (.forallE (.iff
  (rel (𝒞 := 𝒞) D.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
  (.conj (.mem (.bound 2) T.weaken.weaken.weaken) (.conj (.mem (.bound 1) w.weaken.weaken.weaken)
    (.conj (.mem .newest T.weaken.weaken.weaken)
      (fseq_end_m (𝒞 := 𝒞) w.weaken.weaken.weaken .newest (.bound 2) (.bound 1))))))))
derive_free_closed childGraph

theorem childGraph_semantics {n} (hE : Extensional M) (ρ : Env M n) (w T D : Term n) :
    Formula.satisfies ρ (childGraph (𝒞 := 𝒞) w T D) ↔ ChildGraph I (w.eval ρ) (T.eval ρ) (D.eval ρ) := by
  simp only [childGraph, ChildGraph, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    rel_semantics I, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem childGraph_exists (hZF : M.Models ZF) (w T : M.Domain) : ∃ D, ChildGraph I w T D := by
  obtain ⟨WT, hWT⟩ := ZF.exists_cartesianProduct hZF I w T
  obtain ⟨B, hB⟩ := ZF.exists_cartesianProduct hZF I T WT
  let ρ : Env M 1 := ⟨fun _ => w, fun _ => w⟩
  let φ : UnarySchema 1 := {body := .existsE (.existsE (.existsE (.existsE (.conj
    (𝒞.code (.bound 4) (.bound 3) .newest) (.conj (𝒞.code .newest (.bound 2) (.bound 1))
      (fseq_end_m (𝒞 := 𝒞) (.bound 5) (.bound 1) (.bound 3) (.bound 2)))))))}
  have hφ p : φ.denote ρ p ↔ ∃ s n t nt, I.Codes p s nt ∧ I.Codes nt n t ∧ Fseq_end_d I w t s n := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, fseq_end_sat_l I hZF.1]
    rfl
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨D, fun s n t => ⟨?_, ?_⟩⟩
  · rintro ⟨nt, hnt, p, hp, hpD⟩
    obtain ⟨s', hs, nt', hntWT, hp'⟩ := (hB p).mp ((hD p).mp hpD).1
    obtain ⟨rfl, rfl⟩ := I.injective hp hp'
    obtain ⟨n', hn, t', ht, hnt'⟩ := (hWT nt).mp hntWT
    obtain ⟨rfl, rfl⟩ := I.injective hnt hnt'
    obtain ⟨s'', n'', t'', nt'', hp'', hnt'', he⟩ := (hφ p).mp ((hD p).mp hpD).2
    obtain ⟨rfl, rfl⟩ := I.injective hp hp''
    obtain ⟨rfl, rfl⟩ := I.injective hnt hnt''
    exact ⟨hs, hn, ht, he⟩
  · rintro ⟨hs, hn, ht, he⟩
    obtain ⟨nt, hnt⟩ := I.total n t
    obtain ⟨p, hp⟩ := I.total s nt
    exact ⟨nt, hnt, p, hp, (hD p).mpr ⟨(hB p).mpr ⟨s, hs, nt,
      (hWT nt).mpr ⟨n, hn, t, ht, hnt⟩, hp⟩, (hφ p).mpr ⟨s, n, t, nt, hp, hnt, he⟩⟩⟩

theorem labels_contract {w S A z R T labels L : M.Domain}
    (hT : Tree I w S A z R T labels) (hL : Leaves I T labels L) :
    ForcingCountableTreeAlgebra.Labels I T A L labels := by
  refine ⟨hT.2.2.2.2.1, (fun s a ha => ?_), ?_⟩
  · have h := hT.2.2.2.2.2.1 s a ha
    exact ⟨h.1, fun hs => ((hL s).mp hs).2 ⟨a, ha⟩, h.2⟩
  · intro s hs hn
    exact Classical.byContradiction (fun h => hn ((hL s).mpr ⟨hs, h⟩))

theorem children_contract (hZF : M.Models ZF) {w S A z R T labels L D : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hR : Edges I w S R) (hT : Tree I w S A z R T labels)
    (hL : Leaves I T labels L) (hD : ChildGraph I w T D) :
    ForcingCountableTreeAlgebra.Children I T R w L D := by
  intro s hs hn n hnw
  have hl : ∃ a, M.PairMember I s a labels := (labels_contract I hT hL).2.2 s hs hn
  obtain ⟨k, hk, hsf⟩ := (hS s).mp (hT.1 s hs)
  obtain ⟨m, t, hm, htf, he⟩ := fseq_end_exists_l I hZF hw hk hsf hnw
  have htS := (hS t).mpr ⟨m, hm, htf⟩
  have ht := (hT.2.2.2.2.2.2 s hs t htS ⟨n, he⟩).mpr hl
  refine ⟨⟨t, (hD s n t).mpr ⟨hs, hnw, ht, he⟩⟩, (fun t ht => ?_), ?_⟩
  · have h := (hD s n t).mp ht
    exact ⟨h.2.2.1, (hR.2 t s).mpr ⟨hT.1 s hs, hT.1 t h.2.2.1, n, h.2.2.2⟩⟩
  · intro t u ht hu
    exact fseq_end_rebuild_l I hZF.1 ((hD s n t).mp ht).2.2.2 ((hD s n u).mp hu).2.2.2

/-- Actual argument graph: append the child INDEX, not merely any child edge. -/
def Arguments (w X V s g : M.Domain) : Prop := M.IsSetFunctionFromTo I g w X ∧
  ∀ n x, M.PairMember I n x g ↔ M.mem n w ∧ ∃ t, Fseq_end_d I w t s n ∧ M.PairMember I t x V

def arguments {n} (w X V s g : Term n) : Formula 1 n := .conj (Formula.isFunctionFromTo 𝒞 g w X)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
    (.conj (.mem (.bound 1) w.weaken.weaken) (.existsE (.conj
      (fseq_end_m (𝒞 := 𝒞) w.weaken.weaken.weaken .newest s.weaken.weaken.weaken (.bound 2))
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) V.weaken.weaken.weaken)))))))
derive_free_closed arguments

theorem arguments_semantics {n} (hE : Extensional M) (ρ : Env M n) (w X V s g : Term n) :
    Formula.satisfies ρ (arguments (𝒞 := 𝒞) w X V s g) ↔
      Arguments I (w.eval ρ) (X.eval ρ) (V.eval ρ) (s.eval ρ) (g.eval ρ) := by
  simp only [arguments, Arguments, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, fseq_end_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

theorem arguments_iff {w T X D V s g : M.Domain} (hD : ChildGraph I w T D)
    (hV : M.IsSetFunctionFromTo I V T X) (hs : M.mem s T) :
    ForcingCountableTreeAlgebra.Arguments I w X D V s g ↔ Arguments I w X V s g := by
  have core n (hn : M.mem n w) x :
      (∃ t, Values I D s n t ∧ M.PairMember I t x V) ↔
        ∃ t, Fseq_end_d I w t s n ∧ M.PairMember I t x V := by
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, ((hD s n t).mp ht).2.2.2, hx⟩
    · rintro ⟨t, he, hx⟩
      exact ⟨t, (hD s n t).mpr ⟨hs, hn, hV.input_mem_of_pairMember hx, he⟩, hx⟩
  exact and_congr_right (fun _ => forall_congr' fun n => forall_congr' fun x =>
    iff_congr Iff.rfl (and_congr_right fun hn => core n hn x))

/-- Evaluation written directly in the actual source leaf and indexed-child syntax. -/
def Evaluation (w T X labels op base V : M.Domain) : Prop := M.IsSetFunctionFromTo I V T X ∧
  ∀ s x, M.PairMember I s x V →
    ((¬ ∃ a, M.PairMember I s a labels) ∧ x = base) ∨
    ∃ a g, M.PairMember I s a labels ∧ Arguments I w X V s g ∧ Values I op a g x

def evaluation {n} (w T X labels op base V : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 V T X) (.forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken)
    (.disj (.conj (.neg (.existsE (Formula.orderedPairMem 𝒞 (.bound 2) .newest labels.weaken.weaken.weaken)))
      (Formula.extensionalEq .newest base.weaken.weaken))
      (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) labels.weaken.weaken.weaken.weaken)
        (.conj (arguments (𝒞 := 𝒞) w.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken
          V.weaken.weaken.weaken.weaken (.bound 3) .newest)
          (rel (𝒞 := 𝒞) op.weaken.weaken.weaken.weaken (.bound 1) .newest (.bound 2))))))))))
derive_free_closed evaluation

theorem evaluation_semantics {n} (hE : Extensional M) (ρ : Env M n) (w T X labels op base V : Term n) :
    Formula.satisfies ρ (evaluation (𝒞 := 𝒞) w T X labels op base V) ↔
      Evaluation I (w.eval ρ) (T.eval ρ) (X.eval ρ) (labels.eval ρ) (op.eval ρ) (base.eval ρ) (V.eval ρ) := by
  simp only [evaluation, Evaluation, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, arguments_semantics I hE, rel_semantics I,
    Definitional.Term.eval_weaken]
  rfl

theorem evaluation_iff {w T X labels L D op base V : M.Domain}
    (hL : Leaves I T labels L) (hD : ChildGraph I w T D) :
    ForcingCountableTreeAlgebra.Evaluation I w T X L labels D op base V ↔ Evaluation I w T X labels op base V := by
  constructor
  · rintro ⟨hV, hEval⟩
    refine ⟨hV, fun s x hx => ?_⟩
    rcases (hEval s x hx).2.2.2 with ⟨hsL, he⟩ | ⟨_, a, g, ha, hg, hop⟩
    · exact Or.inl ⟨((hL s).mp hsL).2, he⟩
    · exact Or.inr ⟨a, g, ha, (arguments_iff I hD hV (hV.input_mem_of_pairMember hx)).mp hg, hop⟩
  · rintro ⟨hV, hEval⟩
    refine ⟨hV, fun s x hx => ?_⟩
    have hs := hV.input_mem_of_pairMember hx
    refine ⟨⟨hV.1, fun s x hx => ⟨hV.input_mem_of_pairMember hx, hV.output_mem_of_pairMember hx⟩⟩,
      hs, hV.output_mem_of_pairMember hx, ?_⟩
    rcases hEval s x hx with ⟨hn, he⟩ | ⟨a, g, ha, hg, hop⟩
    · exact Or.inl ⟨(hL s).mpr ⟨hs, hn⟩, he⟩
    · exact Or.inr ⟨fun hsL => ((hL s).mp hsL).2 ⟨a, ha⟩,
        a, g, ha, (arguments_iff I hD hV hs).mpr hg, hop⟩

/-- All generic evaluator premises are now supplied by the actual tree data. -/
theorem evaluate (hZF : M.Models ZF) {w S A z R T labels X op base : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hR : Edges I w S R) (hT : Tree I w S A z R T labels)
    (ho : ForcingCountableTreeAlgebra.Operation I w A X op) (hb : M.mem base X) :
    ∃ V, Evaluation I w T X labels op base V ∧ ∀ W, Evaluation I w T X labels op base W → W = V := by
  obtain ⟨L, hL⟩ := leaves_exists I hZF T labels
  obtain ⟨D, hD⟩ := childGraph_exists I hZF w T
  obtain ⟨V, hV, hu⟩ := ForcingCountableTreeAlgebra.evaluate I hZF hT.2.2.2.1
    (labels_contract I hT hL) (children_contract I hZF hw hS hR hT hL hD) ho hb
  exact ⟨V, (evaluation_iff I hL hD).mp hV, fun W hW => hu W ((evaluation_iff I hL hD).mpr hW)⟩


def RootValue (w X op base z c x : M.Domain) : Prop := ∃ T labels V,
  I.Codes c T labels ∧ Evaluation I w T X labels op base V ∧ M.PairMember I z x V

def rootValue {n} (w X op base z c x : Term n) : Formula 1 n := .existsE (.existsE (.existsE (.conj
  (𝒞.code c.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
    (evaluation (𝒞 := 𝒞) w.weaken.weaken.weaken (.bound 2) X.weaken.weaken.weaken (.bound 1)
      op.weaken.weaken.weaken base.weaken.weaken.weaken .newest)
    (Formula.orderedPairMem 𝒞 z.weaken.weaken.weaken x.weaken.weaken.weaken .newest)))))
derive_free_closed rootValue

theorem rootValue_semantics {n} (hE : Extensional M) (ρ : Env M n) (w X op base z c x : Term n) :
    Formula.satisfies ρ (rootValue (𝒞 := 𝒞) w X op base z c x) ↔
      RootValue I (w.eval ρ) (X.eval ρ) (op.eval ρ) (base.eval ρ) (z.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [rootValue, RootValue, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, evaluation_semantics I hE, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  rfl

theorem root_exists_unique (hZF : M.Models ZF) {w S A z R C X op base c : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (ho : ForcingCountableTreeAlgebra.Operation I w A X op) (hb : M.mem base X) (hc : M.mem c C) :
    ∃ x, M.mem x X ∧ RootValue I w X op base z c x ∧ ∀ y, RootValue I w X op base z c y → y = x := by
  obtain ⟨T, labels, hcode, hT⟩ := (hC c).mp hc
  obtain ⟨V, hV, hu⟩ := evaluate I hZF hw hS hR hT ho hb
  obtain ⟨x, hx, hz⟩ := hV.1.2.2 z hT.2.1
  refine ⟨x, hx, ⟨T, labels, V, hcode, hV, hz⟩, ?_⟩
  rintro y ⟨U, F, W, hcode', hW, hy⟩
  obtain ⟨rfl, rfl⟩ := I.injective hcode hcode'
  have e := hu W hW
  subst W
  exact hV.1.1.2 z y x hy hz

def Roots (w X op base z C E : M.Domain) : Prop := M.IsSetFunctionFromTo I E C X ∧
  ∀ c x, M.PairMember I c x E ↔ M.mem c C ∧ RootValue I w X op base z c x

def roots {n} (w X op base z C E : Term n) : Formula 1 n := .conj (Formula.isFunctionFromTo 𝒞 E C X)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken)
    (.conj (.mem (.bound 1) C.weaken.weaken)
      (rootValue (𝒞 := 𝒞) w.weaken.weaken X.weaken.weaken op.weaken.weaken base.weaken.weaken
        z.weaken.weaken (.bound 1) .newest)))))
derive_free_closed roots

theorem roots_semantics {n} (hE : Extensional M) (ρ : Env M n) (w X op base z C E : Term n) :
    Formula.satisfies ρ (roots (𝒞 := 𝒞) w X op base z C E) ↔
      Roots I (w.eval ρ) (X.eval ρ) (op.eval ρ) (base.eval ρ) (z.eval ρ) (C.eval ρ) (E.eval ρ) := by
  simp only [roots, Roots, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, rootValue_semantics I hE, Definitional.Term.eval_weaken]
  rfl

/-- Source evaluate is now ONE internal function on the full actual tree carrier. -/
theorem roots_exists (hZF : M.Models ZF) {w S A z R C X op base : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (ho : ForcingCountableTreeAlgebra.Operation I w A X op) (hb : M.mem base X) :
    ∃ E, Roots I w X op base z C E := by
  let ρ : Env M 5 := ((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push X).push op).push base).push z
  let φ : BinarySchema 5 := {body := (rootValue (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest)}
  have hφ c x : φ.denote ρ c x ↔ RootValue I w X op base z c x := by
    simp only [φ, BinarySchema.denote, rootValue_semantics I hZF.1]
    rfl
  obtain ⟨E, hE, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := X)
    (by
      intro c hc
      obtain ⟨x, _, hx, _⟩ := root_exists_unique I hZF hw hS hR hC ho hb hc
      exact ⟨x, (hφ c x).mpr hx⟩)
    (by
      intro c hc x y hx hy
      obtain ⟨v, _, _, hu⟩ := root_exists_unique I hZF hw hS hR hC ho hb hc
      exact (hu x ((hφ c x).mp hx)).trans (hu y ((hφ c y).mp hy)).symm)
    (by
      intro c x _ hx
      obtain ⟨_, _, V, _, hV, hz⟩ := (hφ c x).mp hx
      exact hV.1.output_mem_of_pairMember hz)
  exact ⟨E, hE, fun c x => (he c x).trans (and_congr_right fun _ => hφ c x)⟩

theorem root_leaf {w X op base z c x : M.Domain} (hz : ∀ p, ¬ M.mem p z)
    (hc : LeafCode I z c) (hx : RootValue I w X op base z c x) : x = base := by
  obtain ⟨T, he, _⟩ := hc
  obtain ⟨U, labels, V, he', hV, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := I.injective he he'
  rcases hV.2 z x hx with ⟨_, h⟩ | ⟨a, _, ⟨p, _, hp⟩, _, _⟩
  · exact h
  · exact (hz p hp).elim

/-- The exact source root evaluator exists for all actual internal tree codes. -/
def rootsSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 9 (.imp (Formula.isOmega (.bound 0))
    (.imp (ExistingFiniteSequenceBounds.fseq_space_m (𝒞 := 𝒞) (.bound 0) (.bound 0) (.bound 1))
    (.imp (edges (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 4))
    (.imp (carrier (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
    (.imp (ForcingCountableTreeAlgebra.operationFormula (𝒞 := 𝒞) (.bound 0) (.bound 2) (.bound 6) (.bound 7))
    (.imp (.mem (.bound 8) (.bound 6))
    (.existsE (roots (𝒞 := 𝒞) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 4) (.bound 6) .newest))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
theorem roots_models (hZF : M.Models ZF) : M.SatisfiesSentence (rootsSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    ExistingFiniteSequenceBounds.fseq_space_sat_l I hZF.1, edges_semantics I hZF.1, carrier_semantics I hZF.1,
    ForcingCountableTreeAlgebra.operation_semantics I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, roots_semantics I hZF.1]
  exact fun hw hS hR hC ho hb => roots_exists I hZF hw hS hR hC ho hb

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem roots_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (rootsSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (roots_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeValues
