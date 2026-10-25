/- Object adaptation of pinned ForcingNames.lean:239-278 and Name.smul_pair.
The literal two-element name uses the native pair constructor. Its evaluation
and condition-map laws consume the accepted source recursions, not new ones. -/
import PPAC.Migration.ForcingConditionAction

namespace PPAC.Migration.ForcingPairName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal unordered pair of the two original Kuratowski edges. -/
def pairName {n : Nat} (t sigma tau output : Fin n) : Formula n :=
  .ex (.ex ((PairSyntax.ordered (Fin.last n).castSucc sigma.castSucc.castSucc t.castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last (n+1)) tau.castSucc.castSucc t.castSucc.castSucc).conj
      (PairSyntax.pair output.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))))))

def PairName (t sigma tau output : M.Carrier .set) : Prop :=
  ∃ a b, PureKuratowski.Code M a sigma t ∧ PureKuratowski.Code M b tau t ∧
    PureKuratowski.Pair M output a b

theorem pairName_semantics {n : Nat} (v : Fin n → M.Carrier .set) (t sigma tau output : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (pairName t sigma tau output) ↔
      PairName (v t) (v sigma) (v tau) (v output) := by
  simp only [pairName, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_pair,
    Fin.lastCases_last, Fin.lastCases_castSucc, PairName]
  rfl

theorem exists_pairName (hM : FirstOrder.Theory.Models M nativeZF) (t sigma tau : M.Carrier .set) :
    ∃ output, PairName t sigma tau output := by
  obtain ⟨a, ha⟩ := KuratowskiZF.exists_code hM sigma t
  obtain ⟨b, hb⟩ := KuratowskiZF.exists_code hM tau t
  obtain ⟨output, ho⟩ := SetTheory.KP.exists_pair
    (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) a b
  exact ⟨output, a, b, ha, hb, ho⟩

theorem mem_pairName (hM : FirstOrder.Theory.Models M nativeZF)
    {t sigma tau output : M.Carrier .set} (h : PairName t sigma tau output) (z : M.Carrier .set) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z output ↔
      PureKuratowski.Code M z sigma t ∨ PureKuratowski.Code M z tau t := by
  obtain ⟨a, b, ha, hb, ho⟩ := h
  constructor
  · intro hz
    rcases (ho z).mp hz with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hb
  · intro hz
    apply (ho z).mpr
    exact hz.elim (fun h => Or.inl (KuratowskiZF.code_unique hM h ha))
      (fun h => Or.inr (KuratowskiZF.code_unique hM h hb))

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {t sigma tau x y : M.Carrier .set} (hx : PairName t sigma tau x) (hy : PairName t sigma tau y) : x = y :=
  (ModelTransfer.extensionality hM).eq_of_same_members x y
    (fun z => (mem_pairName hM hx z).trans (mem_pairName hM hy z).symm)

theorem edge_pairName (hM : FirstOrder.Theory.Models M nativeZF)
    {t sigma tau output : M.Carrier .set} (h : PairName t sigma tau output) (child condition : M.Carrier .set) :
    PureKuratowski.PairMember M child condition output ↔ (child = sigma ∨ child = tau) ∧ condition = t := by
  constructor
  · rintro ⟨z, hz, hm⟩
    rcases (mem_pairName hM h z).mp hm with hs | ht
    · obtain ⟨hc, hp⟩ := PureKuratowski.code_injective hz hs
      exact ⟨Or.inl hc, hp⟩
    · obtain ⟨hc, hp⟩ := PureKuratowski.code_injective hz ht
      exact ⟨Or.inr hc, hp⟩
  · rintro ⟨hc, hp⟩
    obtain ⟨z, hz⟩ := KuratowskiZF.exists_code hM child condition
    refine ⟨z, hz, (mem_pairName hM h z).mpr ?_⟩
    subst condition
    rcases hc with hs | ht
    · exact Or.inl (hs ▸ hz)
    · exact Or.inr (ht ▸ hz)

theorem isName (hM : FirstOrder.Theory.Models M nativeZF)
    {P t sigma tau output : M.Carrier .set} (h : PairName t sigma tau output)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (hs : ForcingNames.IsName P sigma) (hu : ForcingNames.IsName P tau) : ForcingNames.IsName P output := by
  apply ForcingNames.intro_name hM P output
  intro z hz
  rcases (mem_pairName hM h z).mp hz with hCode | hCode
  · exact ⟨sigma, t, hCode, ht, hs⟩
  · exact ⟨tau, t, hCode, ht, hu⟩

theorem evaluate_pairName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {p : Formula (n+1)} {params : Fin n → M.Carrier .set}
    {t sigma tau name x y value : M.Carrier .set} (h : PairName t sigma tau name)
    (ht : ForcingClassEvaluation.Predicate p params t)
    (hs : ForcingClassEvaluation.Evaluated p params sigma x)
    (hu : ForcingClassEvaluation.Evaluated p params tau y)
    (hv : ForcingClassEvaluation.Evaluated p params name value) : PureKuratowski.Pair M value x y := by
  intro z
  constructor
  · intro hz
    obtain ⟨child, condition, he, _, hc⟩ := (ForcingClassEvaluation.mem_evaluation hM hv z).mp hz
    obtain ⟨he, _⟩ := (edge_pairName hM h child condition).mp he
    rcases he with he | he
    · subst child
      exact Or.inl (ForcingClassEvaluation.unique hM hc hs)
    · subst child
      exact Or.inr (ForcingClassEvaluation.unique hM hc hu)
  · intro hz
    rcases hz with hx | hy
    · subst z
      exact (ForcingClassEvaluation.mem_evaluation hM hv x).mpr
        ⟨sigma, t, (edge_pairName hM h sigma t).mpr ⟨Or.inl rfl, rfl⟩, ht, hs⟩
    · subst z
      exact (ForcingClassEvaluation.mem_evaluation hM hv y).mpr
        ⟨tau, t, (edge_pairName hM h tau t).mpr ⟨Or.inr rfl, rfl⟩, ht, hu⟩

theorem map_pairName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : ForcingMapConditions.IsFunction f params)
    {t sigma tau name q x y output : M.Carrier .set} (h : PairName t sigma tau name)
    (ht : ForcingMapConditions.MapRel f params t q)
    (hs : ForcingMapConditions.Mapped f params sigma x)
    (hu : ForcingMapConditions.Mapped f params tau y)
    (ho : ForcingMapConditions.Mapped f params name output) : PairName q x y output := by
  obtain ⟨target, htarget⟩ := exists_pairName hM q x y
  have heq : output = target := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨child, condition, v, r, he, hv, hr, hc⟩ := (ForcingMapConditions.mem_mapping hM hf ho z).mp hz
      obtain ⟨hChildCases, hp⟩ := (edge_pairName hM h child condition).mp he
      subst condition
      have hrq := ForcingMapConditions.function_unique hf t r q hr ht
      subst r
      apply (mem_pairName hM htarget z).mpr
      rcases hChildCases with hLeft | hRight
      · subst child
        exact Or.inl ((ForcingMapConditions.unique hM hf hv hs) ▸ hc)
      · subst child
        exact Or.inr ((ForcingMapConditions.unique hM hf hv hu) ▸ hc)
    · intro hz
      apply (ForcingMapConditions.mem_mapping hM hf ho z).mpr
      rcases (mem_pairName hM htarget z).mp hz with hc | hc
      · exact ⟨sigma, t, x, q, (edge_pairName hM h sigma t).mpr ⟨Or.inl rfl, rfl⟩, hs, ht, hc⟩
      · exact ⟨tau, t, y, q, (edge_pairName hM h tau t).mpr ⟨Or.inr rfl, rfl⟩, hu, ht, hc⟩
  exact heq.symm ▸ htarget

def existenceSentence : Source.Sentence := (Formula.ex (pairName (0 : Fin 4) 1 2 3)).close

def uniquenessSentence : Source.Sentence :=
  ((pairName (0 : Fin 5) 1 2 3).imp ((pairName 0 1 2 4).imp (.equal 3 4))).close

def edgeSentence : Source.Sentence :=
  ((pairName (0 : Fin 6) 1 2 3).imp ((Source.SetLanguage.edge 3 4 5).iff
    (((Formula.equal 4 1).disj (.equal 4 2)).conj (.equal 5 0)))).close

def nameSentence : Source.Sentence :=
  ((pairName (1 : Fin 5) 2 3 4).imp ((Formula.mem 1 0).imp
    ((ForcingNames.isName 0 2).imp ((ForcingNames.isName 0 3).imp (ForcingNames.isName 0 4))))).close

def evaluationSentence {n : Nat} (p : Formula (n+1)) (t sigma tau name x y value : Fin n) : Source.Sentence :=
  ((pairName t sigma tau name).imp ((MinimalPredicates.pred p id t).imp
    ((ForcingClassEvaluation.evaluation p id sigma x).imp
      ((ForcingClassEvaluation.evaluation p id tau y).imp
        ((ForcingClassEvaluation.evaluation p id name value).imp (PairSyntax.pair value x y)))))).close

def mappingSentence {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n) : Source.Sentence :=
  ((ForcingMapConditions.function f id).imp ((pairName t sigma tau name).imp
    ((ReplacementPredicates.rel f id t q).imp ((ForcingMapConditions.mapping f id sigma x).imp
      ((ForcingMapConditions.mapping f id tau y).imp ((ForcingMapConditions.mapping f id name output).imp
        (pairName q x y output))))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, ho⟩ := exists_pairName hM (v 0) (v 1) (v 2)
  refine ⟨output, ?_⟩
  let env : Fin 4 → M.Carrier .set := Fin.lastCases output v
  apply (pairName_semantics (M := M) env 0 1 2 3).mpr
  exact ho

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hx hy
  exact unique hM ((pairName_semantics (M := M) v 0 1 2 3).mp hx) ((pairName_semantics (M := M) v 0 1 2 4).mp hy)

theorem edge_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence edgeSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := edge_pairName hM ((pairName_semantics (M := M) v 0 1 2 3).mp h) (v 4) (v 5)
  have hl := KuratowskiZF.source_edge (M := M) v 3 4 5
  exact ⟨fun hz => he.mp (hl.mp hz), fun hz => hl.mpr (he.mpr hz)⟩

theorem name_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence nameSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h ht hs hu
  exact (ForcingNames.isName_semantics (M := M) v 0 4).mpr
    (isName hM ((pairName_semantics (M := M) v 1 2 3 4).mp h) ht
      ((ForcingNames.isName_semantics (M := M) v 0 2).mp hs) ((ForcingNames.isName_semantics (M := M) v 0 3).mp hu))

theorem evaluation_models {n : Nat} (p : Formula (n+1)) (t sigma tau name x y value : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (evaluationSentence p t sigma tau name x y value)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h ht hs hu hv
  exact (KuratowskiZF.source_pair (M := M) v value x y).mpr
    (evaluate_pairName hM ((pairName_semantics (M := M) v t sigma tau name).mp h)
      ((ForcingClassEvaluation.predicate_semantics (M := M) v p id t).mp ht)
      ((ForcingClassEvaluation.evaluation_semantics (M := M) v p id sigma x).mp hs)
      ((ForcingClassEvaluation.evaluation_semantics (M := M) v p id tau y).mp hu)
      ((ForcingClassEvaluation.evaluation_semantics (M := M) v p id name value).mp hv))

theorem mapping_models {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (mappingSentence f t sigma tau name q x y output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hf h ht hs hu ho
  exact (pairName_semantics (M := M) v q x y output).mpr
    (map_pairName hM ((ForcingMapConditions.function_semantics (M := M) v f id).mp hf)
      ((pairName_semantics (M := M) v t sigma tau name).mp h)
      ((ForcingMapConditions.rel_semantics (M := M) v f id t q).mp ht)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id sigma x).mp hs)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id tau y).mp hu)
      ((ForcingMapConditions.mapping_semantics (M := M) v f id name output).mp ho))

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)
theorem uniqueness_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)
theorem edge_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence edgeSentence) :=
  ModelTransfer.derives (fun _ hM => edge_models hM)
theorem name_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence nameSentence) :=
  ModelTransfer.derives (fun _ hM => name_models hM)
theorem evaluation_kernel_certificate {n : Nat} (p : Formula (n+1)) (t sigma tau name x y value : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationSentence p t sigma tau name x y value)) :=
  ModelTransfer.derives (fun _ hM => evaluation_models p t sigma tau name x y value hM)
theorem mapping_kernel_certificate {n : Nat} (f : Formula (n+2)) (t sigma tau name q x y output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (mappingSentence f t sigma tau name q x y output)) :=
  ModelTransfer.derives (fun _ hM => mapping_models f t sigma tau name q x y output hM)

/-- Original Name.smul_pair: the action fixes the distinguished condition. -/
theorem action_pairName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : ForcingConditionGraphs.Endomap (params P) (params r))
    {t sigma tau name x y output : M.Carrier .set} (h : PairName t sigma tau name)
    (ht : ForcingConditionAction.Act (params P) (params r) t t)
    (hs : ForcingMapConditions.Mapped (ForcingConditionAction.actFormula P r) params sigma x)
    (hu : ForcingMapConditions.Mapped (ForcingConditionAction.actFormula P r) params tau y)
    (ho : ForcingMapConditions.Mapped (ForcingConditionAction.actFormula P r) params name output) :
    PairName t x y output :=
  map_pairName hM (ForcingConditionAction.act_function params P r hr) h
    ((ForcingConditionAction.relation_semantics params P r t t).mpr ht) hs hu ho

def actionSentence {n : Nat} (P r t sigma tau name x y output : Fin n) : Source.Sentence :=
  ((ForcingConditionGraphs.endomap P r).imp ((ForcingConditionAction.act P r t t).imp
    ((pairName t sigma tau name).imp
      ((ForcingMapConditions.mapping (ForcingConditionAction.actFormula P r) id sigma x).imp
        ((ForcingMapConditions.mapping (ForcingConditionAction.actFormula P r) id tau y).imp
          ((ForcingMapConditions.mapping (ForcingConditionAction.actFormula P r) id name output).imp
            (pairName t x y output))))))).close

theorem action_models {n : Nat} (P r t sigma tau name x y output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (actionSentence P r t sigma tau name x y output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr ht h hs hu ho
  exact (pairName_semantics (M := M) v t x y output).mpr
    (action_pairName hM v P r ((ForcingConditionGraphs.endomap_semantics (M := M) v P r).mp hr)
      ((pairName_semantics (M := M) v t sigma tau name).mp h)
      ((ForcingConditionAction.act_semantics (M := M) v P r t t).mp ht)
      ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id sigma x).mp hs)
      ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id tau y).mp hu)
      ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id name output).mp ho))

theorem action_kernel_certificate {n : Nat} (P r t sigma tau name x y output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (actionSentence P r t sigma tau name x y output)) :=
  ModelTransfer.derives (fun _ hM => action_models P r t sigma tau name x y output hM)

end PPAC.Migration.ForcingPairName
