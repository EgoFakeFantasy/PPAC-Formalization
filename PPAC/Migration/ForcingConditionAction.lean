/- Pinned ForcingNames.ConditionAction.actCode and Name.act.
An internal permutation graph acts on its condition set and is extended by
identity on every other set code, exactly as in source lines 361-393. -/
import PPAC.Migration.ForcingConditionGraphs

namespace PPAC.Migration.ForcingConditionAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingConditionGraphs
open ForcingMapConditions (MapRel IsFunction Mapped mapping)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def act {m : Nat} (P r x y : Fin m) : Formula m :=
  ((Formula.mem x P).conj (Source.SetLanguage.edge r x y)).disj
    ((Formula.mem x P).neg.conj (.equal x y))

def Act (P r x y : M.Carrier .set) : Prop :=
  ((Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ PureKuratowski.PairMember M x y r) ∨
    (¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ x = y)

theorem act_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (act P r x y) ↔
      Act (v P) (v r) (v x) (v y) := by
  simp only [act, Source.Formula.neg, Formula.Realize, KuratowskiZF.source_edge, Act]

def actFormula {n : Nat} (P r : Fin n) : Formula (n+2) :=
  act P.castSucc.castSucc r.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))

theorem relation_semantics {n : Nat} (params : Fin n → M.Carrier .set) (P r : Fin n) (x y : M.Carrier .set) :
    MapRel (actFormula P r) params x y ↔ Act (params P) (params r) x y := by
  simp only [MapRel, actFormula, act_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

theorem act_inside {P r x y : M.Carrier .set} (hx : (Definitional.Project.FirstOrderSemantics.reduct M).mem x P) :
    Act P r x y ↔ PureKuratowski.PairMember M x y r := by
  exact ⟨fun h => h.elim And.right (fun h => False.elim (h.1 hx)), fun h => Or.inl ⟨hx, h⟩⟩

theorem act_outside {P r x y : M.Carrier .set} (hx : ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x P) :
    Act P r x y ↔ x = y := by
  exact ⟨fun h => h.elim (fun h => False.elim (hx h.1)) And.right, fun h => Or.inr ⟨hx, h⟩⟩

theorem act_into {P r x y : M.Carrier .set} (hr : Endomap P r)
    (hx : (Definitional.Project.FirstOrderSemantics.reduct M).mem x P) (h : Act P r x y) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y P :=
  hr.2 x y ((act_inside hx).mp h)

theorem act_function {n : Nat} (params : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : Endomap (params P) (params r)) : IsFunction (actFormula P r) params := by
  classical
  intro x
  by_cases hx : (Definitional.Project.FirstOrderSemantics.reduct M).mem x (params P)
  · obtain ⟨y, hy, hu⟩ := hr.1.2 x hx
    refine ⟨y, (relation_semantics params P r x y).mpr ((act_inside hx).mpr hy), ?_⟩
    intro z hz
    exact hu z ((act_inside hx).mp ((relation_semantics params P r x z).mp hz))
  · refine ⟨x, (relation_semantics params P r x x).mpr ((act_outside hx).mpr rfl), ?_⟩
    intro z hz
    exact ((act_outside hx).mp ((relation_semantics params P r x z).mp hz)).symm

theorem act_identity {P r : M.Carrier .set} (hr : IdentityGraph P r) (x y : M.Carrier .set) :
    Act P r x y ↔ x = y := by
  classical
  by_cases hx : (Definitional.Project.FirstOrderSemantics.reduct M).mem x P
  · rw [act_inside hx, hr x y]
    exact ⟨And.right, fun h => ⟨hx, h⟩⟩
  · exact act_outside hx

theorem act_composition {P r s t : M.Carrier .set} (hs : Endomap P s) (hc : CompositionGraph P r s t)
    (x z : M.Carrier .set) : Act P t x z ↔ ∃ y, Act P s x y ∧ Act P r y z := by
  classical
  by_cases hx : (Definitional.Project.FirstOrderSemantics.reduct M).mem x P
  · constructor
    · intro h
      obtain ⟨_, y, hy, hz⟩ := (hc x z).mp ((act_inside hx).mp h)
      exact ⟨y, (act_inside hx).mpr hy, (act_inside (hs.2 x y hy)).mpr hz⟩
    · rintro ⟨y, hy, hz⟩
      have hy' := (act_inside hx).mp hy
      exact (act_inside hx).mpr ((hc x z).mpr ⟨hx, y, hy', (act_inside (hs.2 x y hy')).mp hz⟩)
  · constructor
    · intro h
      exact ⟨x, (act_outside hx).mpr rfl, (act_outside hx).mpr ((act_outside hx).mp h)⟩
    · rintro ⟨y, hy, hz⟩
      have he := (act_outside hx).mp hy
      subst y
      exact (act_outside hx).mpr ((act_outside hx).mp hz)

theorem act_inverse {P r s : M.Carrier .set} (hr : Endomap P r) (hs : Endomap P s)
    (hi : InverseGraph r s) (x y : M.Carrier .set) : Act P r x y ↔ Act P s y x := by
  constructor
  · rintro (⟨hx, he⟩ | ⟨hx, he⟩)
    · exact Or.inl ⟨hr.2 x y he, (hi x y).mp he⟩
    · subst y
      exact Or.inr ⟨hx, rfl⟩
  · rintro (⟨hy, he⟩ | ⟨hy, he⟩)
    · exact Or.inl ⟨hs.2 y x he, (hi x y).mpr he⟩
    · subst x
      exact Or.inr ⟨hy, rfl⟩

/-- Actual Name.act uses the extended condition formula, not an assumed action. -/
theorem name_preservation (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r : Fin n) (hr : Endomap (params P) (params r))
    {sigma output : M.Carrier .set} (hn : ForcingNames.IsName (params P) sigma)
    (hm : Mapped (actFormula P r) params sigma output) : ForcingNames.IsName (params P) output :=
  ForcingMapLaws.name_preservation hM (act_function params P r hr) (params P) (params P)
    (fun x y hx hy => act_into hr hx ((relation_semantics params P r x y).mp hy)) hn hm

theorem name_identity (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r : Fin n) (hr : IdentityGraph (params P) (params r))
    (sigma : M.Carrier .set) (hn : ForcingNames.IsName (params P) sigma) :
    Mapped (actFormula P r) params sigma sigma := by
  have he : ∀ x y, MapRel (actFormula P r) params x y ↔ MapRel (ForcingMapLaws.identityRelation n) params x y :=
    fun x y => (relation_semantics params P r x y).trans ((act_identity hr x y).trans (ForcingMapLaws.identity_rel params x y).symm)
  exact (ForcingMapLaws.mapping_congr he sigma sigma).mpr (ForcingMapLaws.identity_mapping hM params (params P) sigma hn)

theorem name_composition (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r s t : Fin n)
    (hr : Endomap (params P) (params r)) (hs : Endomap (params P) (params s))
    (hc : CompositionGraph (params P) (params r) (params s) (params t))
    {sigma mid output : M.Carrier .set} (hm : Mapped (actFormula P s) params sigma mid)
    (ho : Mapped (actFormula P r) params mid output) : Mapped (actFormula P t) params sigma output := by
  have he : ∀ x z, MapRel (ForcingMapLaws.compose (actFormula P r) (actFormula P s)) params x z ↔
      MapRel (actFormula P t) params x z := by
    intro x z
    simp only [ForcingMapLaws.compose_rel, relation_semantics (M := M)]
    exact (act_composition hs hc x z).symm
  exact (ForcingMapLaws.mapping_congr he sigma output).mp
    (ForcingMapLaws.composition_mapping hM (act_function params P r hr) (act_function params P s hs) hm ho)

theorem name_inverse (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r s : Fin n)
    (hr : Endomap (params P) (params r)) (hs : Endomap (params P) (params s))
    (hi : InverseGraph (params r) (params s)) {sigma mid output : M.Carrier .set}
    (hn : ForcingNames.IsName (params P) sigma) (hm : Mapped (actFormula P r) params sigma mid)
    (ho : Mapped (actFormula P s) params mid output) : output = sigma := by
  have hfr := act_function params P r hr
  have hfs := act_function params P s hs
  have he : ∀ x z, MapRel (ForcingMapLaws.compose (actFormula P s) (actFormula P r)) params x z ↔
      MapRel (ForcingMapLaws.identityRelation n) params x z := by
    intro x z
    rw [ForcingMapLaws.compose_rel, ForcingMapLaws.identity_rel]
    constructor
    · rintro ⟨y, hy, hz⟩
      have hyx := (relation_semantics params P s y x).mpr
        ((act_inverse hr hs hi x y).mp ((relation_semantics params P r x y).mp hy))
      exact ForcingMapConditions.function_unique hfs y x z hyx hz
    · intro hxz
      subst z
      obtain ⟨y, hy, _⟩ := hfr x
      exact ⟨y, hy, (relation_semantics params P s y x).mpr
        ((act_inverse hr hs hi x y).mp ((relation_semantics params P r x y).mp hy))⟩
  have hId := (ForcingMapLaws.mapping_congr he sigma output).mp (ForcingMapLaws.composition_mapping hM hfs hfr hm ho)
  exact ForcingMapConditions.unique hM (ForcingMapLaws.identity_function params) hId
    (ForcingMapLaws.identity_mapping hM params (params P) sigma hn)

def functionSentence {n : Nat} (P r : Fin n) : Source.Sentence :=
  ((endomap P r).imp (ForcingMapConditions.function (actFormula P r) id)).close

def nameSentence {n : Nat} (P r : Fin n) : Source.Sentence :=
  ((endomap P r).imp (.all ((ForcingNames.isName P.castSucc (Fin.last n)).imp (.ex
    ((mapping (actFormula P r) (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))).conj
      (ForcingNames.isName P.castSucc.castSucc (Fin.last (n+1)))))))).close

def identitySentence {n : Nat} (P r : Fin n) : Source.Sentence :=
  ((identityGraph P r).imp (.all ((ForcingNames.isName P.castSucc (Fin.last n)).imp
    (mapping (actFormula P r) Fin.castSucc (Fin.last n) (Fin.last n))))).close

def compositionAt {n m : Nat} (P r s t : Fin n) (rho : Fin n → Fin m) (sigma : Fin m) : Formula m :=
  .all (.all ((mapping (actFormula P s) (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last m).castSucc).imp
    ((mapping (actFormula P r) (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (mapping (actFormula P t) (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last (m+1))))))

theorem compositionAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (P r s t : Fin n) (rho : Fin n → Fin m) (sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (compositionAt P r s t rho sigma) ↔
      ∀ mid output, Mapped (actFormula P s) (fun i => v (rho i)) (v sigma) mid →
        Mapped (actFormula P r) (fun i => v (rho i)) mid output → Mapped (actFormula P t) (fun i => v (rho i)) (v sigma) output := by
  simp only [compositionAt, Formula.Realize, ForcingMapConditions.mapping_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def compositionSentence {n : Nat} (P r s t : Fin n) : Source.Sentence :=
  ((endomap P r).imp ((endomap P s).imp ((compositionGraph P r s t).imp
    (.all (compositionAt P r s t Fin.castSucc (Fin.last n)))))).close

def inverseSentence {n : Nat} (P r s : Fin n) : Source.Sentence :=
  ((endomap P r).imp ((endomap P s).imp ((inverseGraph r s).imp (.all (.all (.all
    ((ForcingNames.isName P.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc).imp
      ((mapping (actFormula P r) (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
        ((mapping (actFormula P s) (fun i => i.castSucc.castSucc.castSucc)
          (Fin.last (n+1)).castSucc (Fin.last (n+2))).imp
          (.equal (Fin.last (n+2)) (Fin.last n).castSucc.castSucc)))))))))).close

theorem function_models {n : Nat} (P r : Fin n) :
    (Translation.sentence (functionSentence P r)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  exact (ForcingMapConditions.function_semantics v (actFormula P r) id).mpr
    (act_function v P r ((endomap_semantics v P r).mp h))

theorem name_models {n : Nat} (P r : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (nameSentence P r)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h sigma hn
  have hr := (endomap_semantics v P r).mp h
  let currentEnv : Fin (n+1) → M.Carrier .set := Fin.lastCases sigma v
  have hNameSem := ForcingNames.isName_semantics (M := M) currentEnv P.castSucc (Fin.last n)
  have hn' : ForcingNames.IsName (v P) sigma := by
    have hReal : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem currentEnv
        (ForcingNames.isName P.castSucc (Fin.last n)) := hn
    simpa only [currentEnv, Fin.lastCases_last, Fin.lastCases_castSucc] using hNameSem.mp hReal
  obtain ⟨output, hm⟩ := ForcingMapConditions.exists_mapping hM (actFormula P r) v (act_function v P r hr) sigma
  refine ⟨output, ?_, ?_⟩
  · apply (ForcingMapConditions.mapping_semantics (Fin.lastCases output (Fin.lastCases sigma v))
      (actFormula P r) (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hm
  · apply (ForcingNames.isName_semantics (M := M) (Fin.lastCases output (Fin.lastCases sigma v)) P.castSucc.castSucc (Fin.last (n+1))).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using name_preservation hM v P r hr hn' hm

theorem identity_models {n : Nat} (P r : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (identitySentence P r)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h sigma hn
  have hi := (identityGraph_semantics v P r).mp h
  let currentEnv : Fin (n+1) → M.Carrier .set := Fin.lastCases sigma v
  have hNameSem := ForcingNames.isName_semantics (M := M) currentEnv P.castSucc (Fin.last n)
  have hn' : ForcingNames.IsName (v P) sigma := by
    have hReal : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem currentEnv
        (ForcingNames.isName P.castSucc (Fin.last n)) := hn
    simpa only [currentEnv, Fin.lastCases_last, Fin.lastCases_castSucc] using hNameSem.mp hReal
  apply (ForcingMapConditions.mapping_semantics (Fin.lastCases sigma v) (actFormula P r) Fin.castSucc (Fin.last n) (Fin.last n)).mpr
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using name_identity hM v P r hi sigma hn'

theorem composition_models {n : Nat} (P r s t : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (compositionSentence P r s t)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr hs hc sigma
  apply (compositionAt_semantics (Fin.lastCases sigma v) P r s t Fin.castSucc (Fin.last n)).mpr
  intro mid output hm ho
  have hm' : Mapped (actFormula P s) v sigma mid := by simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hm
  have ho' : Mapped (actFormula P r) v mid output := by simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using ho
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using name_composition hM v P r s t
    ((endomap_semantics v P r).mp hr) ((endomap_semantics v P s).mp hs) ((compositionGraph_semantics v P r s t).mp hc) hm' ho'

theorem inverse_models {n : Nat} (P r s : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (inverseSentence P r s)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr hs hi sigma mid output hn hm ho
  let env : Fin (n+3) → M.Carrier .set := Fin.lastCases output (Fin.lastCases mid (Fin.lastCases sigma v))
  have hn' : ForcingNames.IsName (v P) sigma := by
    simpa only [env, Fin.lastCases_last, Fin.lastCases_castSucc] using
      ((ForcingNames.isName_semantics (M := M) env P.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc).mp hn)
  have hm' : Mapped (actFormula P r) v sigma mid := by
    simpa only [env, Fin.lastCases_last, Fin.lastCases_castSucc] using
      ((ForcingMapConditions.mapping_semantics (M := M) env (actFormula P r) (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).mp hm)
  have ho' : Mapped (actFormula P s) v mid output := by
    simpa only [env, Fin.lastCases_last, Fin.lastCases_castSucc] using
      ((ForcingMapConditions.mapping_semantics (M := M) env (actFormula P s) (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n+1)).castSucc (Fin.last (n+2))).mp ho)
  have he := name_inverse hM v P r s ((endomap_semantics v P r).mp hr) ((endomap_semantics v P s).mp hs)
    ((inverseGraph_semantics v r s).mp hi) hn' hm' ho'
  simpa only [Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc] using he

theorem function_kernel_certificate {n : Nat} (P r : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (functionSentence P r)) :=
  ModelTransfer.derives (fun _ _ => function_models P r)
theorem name_kernel_certificate {n : Nat} (P r : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (nameSentence P r)) :=
  ModelTransfer.derives (fun _ hM => name_models P r hM)
theorem identity_kernel_certificate {n : Nat} (P r : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (identitySentence P r)) :=
  ModelTransfer.derives (fun _ hM => identity_models P r hM)
theorem composition_kernel_certificate {n : Nat} (P r s t : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (compositionSentence P r s t)) :=
  ModelTransfer.derives (fun _ hM => composition_models P r s t hM)
theorem inverse_kernel_certificate {n : Nat} (P r s : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (inverseSentence P r s)) :=
  ModelTransfer.derives (fun _ hM => inverse_models P r s hM)

/-- Original Name.evaluate_smul, for the actual identity-outside actCode. -/
theorem name_covariance (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P r : Fin n) (p : Formula (n+1))
    (hr : Endomap (params P) (params r)) {sigma mapped output : M.Carrier .set}
    (hm : Mapped (actFormula P r) params sigma mapped) :
    ForcingClassEvaluation.Evaluated p params mapped output ↔
      ForcingClassEvaluation.Evaluated (ForcingEvaluationCovariance.preimage (actFormula P r) p) params sigma output :=
  ForcingEvaluationCovariance.covariance_iff hM p (act_function params P r hr) hm

def covarianceSentence {n : Nat} (P r : Fin n) (p : Formula (n+1)) : Source.Sentence :=
  ((endomap P r).imp (.all (.all (.all
    ((mapping (actFormula P r) (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).imp
      ((ForcingClassEvaluation.evaluation p (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n+1)).castSucc (Fin.last (n+2))).iff
        (ForcingClassEvaluation.evaluation (ForcingEvaluationCovariance.preimage (actFormula P r) p)
          (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc (Fin.last (n+2))))))))).close

theorem covariance_models {n : Nat} (P r : Fin n) (p : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (covarianceSentence P r p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr sigma mapped output hm
  let env : Fin (n+3) → M.Carrier .set := Fin.lastCases output (Fin.lastCases mapped (Fin.lastCases sigma v))
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  have hm' : Mapped (actFormula P r) v sigma mapped := by
    simpa only [env, rho, Fin.lastCases_last, Fin.lastCases_castSucc] using
      ((ForcingMapConditions.mapping_semantics (M := M) env (actFormula P r) rho
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc).mp hm)
  have he := name_covariance hM v P r p ((endomap_semantics v P r).mp hr) hm' (output := output)
  have hl := ForcingClassEvaluation.evaluation_semantics (M := M) env p rho (Fin.last (n+1)).castSucc (Fin.last (n+2))
  have hx := ForcingClassEvaluation.evaluation_semantics (M := M) env (ForcingEvaluationCovariance.preimage (actFormula P r) p)
    rho (Fin.last n).castSucc.castSucc (Fin.last (n+2))
  simp only [env, rho, Fin.lastCases_last, Fin.lastCases_castSucc] at hl hx
  exact ⟨fun hv => hx.mpr (he.mp (hl.mp hv)), fun hv => hl.mpr (he.mpr (hx.mp hv))⟩

theorem covariance_kernel_certificate {n : Nat} (P r : Fin n) (p : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (covarianceSentence P r p)) :=
  ModelTransfer.derives (fun _ hM => covariance_models P r p hM)

end PPAC.Migration.ForcingConditionAction
