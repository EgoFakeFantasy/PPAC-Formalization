/- Canonical evaluator parameters for the literal original bareStageAt formula.
Reuses the accepted source numeral and omega proofs. No host-selected internal
Nat enumeration or standard-omega assumption is introduced. -/
import PPAC.Migration.ConstructibleHistory
import PPAC.Migration.Internal.SyntaxNumerals
import PPAC.Migration.ObjectOmega

namespace PPAC.Migration.ConstructibleParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source SourceAlgebra SourceLogic
open Internal
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
universe u
variable {A : Type u} {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def numeralValue (E : A → A → Prop) (k : Nat) (x : A) : Prop :=
  Source.Formula.Realize E (fun _ : Fin 1 => x) (SyntaxNumeralSyntax.numeral k 0)

def omegaValue (E : A → A → Prop) (x : A) : Prop :=
  Source.Formula.Realize E (fun _ : Fin 1 => x) (OmegaSyntax.omega 0)

theorem numeral_at (E : A → A → Prop) {n : Nat} (v : Fin n → A) (k : Nat) (x : Fin n) :
    Source.Formula.Realize E v (SyntaxNumeralSyntax.numeral k x) ↔ numeralValue E k (v x) := by
  rw [← SyntaxNumeralSyntax.numeral_rename k (0 : Fin 1) (fun _ => x),
    DefinableMinimaChoice.realize_rename]
  rfl

theorem omega_at (E : A → A → Prop) {n : Nat} (v : Fin n → A) (x : Fin n) :
    Source.Formula.Realize E v (OmegaSyntax.omega x) ↔ omegaValue E (v x) := by
  rw [← OmegaSyntax.omega_rename (0 : Fin 1) (fun _ => x),
    DefinableMinimaChoice.realize_rename]
  rfl

def numeralExistence (k : Nat) : Source.Sentence :=
  ((OmegaSyntax.omega (0 : Fin 1)).imp (SyntaxNumeralSyntax.existsNumeral 0 k)).close

def numeralUniqueness (k : Nat) : Source.Sentence :=
  ((SyntaxNumeralSyntax.numeral k (0 : Fin 2)).imp
    ((SyntaxNumeralSyntax.numeral k 1).imp (.equal 0 1))).close

theorem source_numeral_exists (k : Nat) : Source.Derives (Source.SetLanguage.ZF.at 0) (numeralExistence k) := by
  apply close_derives
  apply Derives.impI
  exact SyntaxNumerals.exists_numeral (ZFContext.add (ZFContext.source_ZF 1) _) k 0 (.hyp (Or.inl rfl))

theorem source_numeral_unique (k : Nat) : Source.Derives (Source.SetLanguage.ZF.at 0) (numeralUniqueness k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SyntaxNumerals.unique (ZFContext.add (ZFContext.add (ZFContext.source_ZF 2) _) _) k 0 1
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem numeral_exists (hM : FirstOrder.Theory.Models M nativeZF) (k : Nat)
    {w : M.Carrier .set} (hw : omegaValue (Project.FirstOrderSemantics.reduct M).mem w) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x w ∧
      numeralValue (Project.FirstOrderSemantics.reduct M).mem k x := by
  have h := (Translation.realizes_sentence M _).mp
    ((ZFReplay.replay (TheoryTransport.sentence (source_numeral_exists k))).semantically_entails M hM)
  have ha := (GodelDefOutput.close_semantics _ _).mp h (fun _ => w)
  have hh := ha hw
  simp only [SyntaxNumeralSyntax.existsNumeral, Source.Formula.Realize, numeral_at,
    Fin.lastCases_last, Fin.lastCases_castSucc] at hh
  exact hh

theorem numeral_unique (hM : FirstOrder.Theory.Models M nativeZF) (k : Nat)
    {x y : M.Carrier .set}
    (hx : numeralValue (Project.FirstOrderSemantics.reduct M).mem k x)
    (hy : numeralValue (Project.FirstOrderSemantics.reduct M).mem k y) : x = y := by
  have h := (Translation.realizes_sentence M _).mp
    ((ZFReplay.replay (TheoryTransport.sentence (source_numeral_unique k))).semantically_entails M hM)
  have ha := (GodelDefOutput.close_semantics _ _).mp h (Source.SetLanguage.args2 x y)
  simp only [Source.Formula.Realize, numeral_at] at ha
  exact ha hx hy

theorem omega_exists (hM : FirstOrder.Theory.Models M nativeZF) :
    ∃ w, omegaValue (Project.FirstOrderSemantics.reduct M).mem w := by
  have h := (Translation.realizes_sentence M _).mp (ObjectOmega.native_existence.semantically_entails M hM)
  change ∃ w, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
    (Fin.lastCases w Fin.elim0) (OmegaSyntax.omega (0 : Fin 1)) at h
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have he : Fin.lastCases w (Fin.elim0 : Fin 0 → M.Carrier .set) = (fun _ : Fin 1 => w) := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
    rfl
  rw [he] at hw
  exact hw

theorem omega_unique (hM : FirstOrder.Theory.Models M nativeZF) {x y : M.Carrier .set}
    (hx : omegaValue (Project.FirstOrderSemantics.reduct M).mem x)
    (hy : omegaValue (Project.FirstOrderSemantics.reduct M).mem y) : x = y := by
  have h := (Translation.realizes_sentence M _).mp (ObjectOmega.native_unique.semantically_entails M hM)
  have ha := (GodelDefOutput.close_semantics _ _).mp h (Source.SetLanguage.args2 x y)
  simp only [Source.Formula.Realize, omega_at] at ha
  exact ha hx hy

/-- Original slots 0,1,2 are varTag, appTag, empty; slots 3..11 are op0..op8. -/
def slotCode (i : Fin 12) : Nat :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | k+3 => k

def conditions : Project.Formula 1 13 :=
  .conj (Project.Formula.conjunction ((List.finRange 12).map (fun i =>
    ProjectSyntax.formula (SyntaxNumeralSyntax.numeral (slotCode i) i.castSucc))))
    (ProjectSyntax.formula (OmegaSyntax.omega 12))

theorem conditions_closed : conditions.FreeClosed := by decide +kernel

theorem conjunction_semantics {N : SetTheory.Structure.{u}} {n : Nat}
    (env : SetTheory.Env N n) (ps : List (Project.Formula 1 n)) :
    Project.Formula.satisfies env (Project.Formula.conjunction ps) ↔
      ∀ p, p ∈ ps → Project.Formula.satisfies env p := by
  induction ps with
  | nil =>
      rw [Project.Formula.conjunction, Project.Formula.satisfies_truth_iff]
      exact ⟨fun _ p hp => False.elim (List.not_mem_nil hp), fun _ => True.intro⟩
  | cons p ps ih =>
      cases ps with
      | nil =>
          change Project.Formula.satisfies env p ↔ _
          constructor
          · intro h q hq
            have he := List.mem_singleton.mp hq
            exact he ▸ h
          · intro h
            exact h p (List.mem_singleton.mpr rfl)
      | cons q qs =>
          rw [Project.Formula.conjunction, Project.Formula.satisfies_conj_iff, ih]
          constructor
          · rintro ⟨hp, hps⟩ r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hp
            · exact hps r hr
          · intro h
            exact ⟨h p (List.mem_cons_self), fun r hr => h r (List.mem_cons_of_mem p hr)⟩
          all_goals simp

theorem conditions_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) :
    Project.Formula.satisfies env conditions ↔
      (∀ i : Fin 12, numeralValue (Project.FirstOrderSemantics.reduct M).mem
        (slotCode i) (env.bound i.castSucc.rev)) ∧
      omegaValue (Project.FirstOrderSemantics.reduct M).mem (env.bound 0) := by
  simp only [conditions, Project.Formula.satisfies_conj_iff, conjunction_semantics]
  have hn (i : Fin 12) : Project.Formula.satisfies env
      (ProjectSyntax.formula (SyntaxNumeralSyntax.numeral (slotCode i) i.castSucc)) ↔
      numeralValue (Project.FirstOrderSemantics.reduct M).mem (slotCode i) (env.bound i.castSucc.rev) := by
    exact (GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM) _ _ _).trans
      (numeral_at _ _ _ _)
  have hw : Project.Formula.satisfies env (ProjectSyntax.formula (OmegaSyntax.omega 12)) ↔
      omegaValue (Project.FirstOrderSemantics.reduct M).mem (env.bound 0) := by
    exact (GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM) _ _ _).trans (omega_at _ _ _)
  rw [hw]
  apply and_congr_left
  intro _
  constructor
  · intro h i
    apply (hn i).mp
    exact h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · intro h p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact (hn i).mpr (h i)

/-- All thirteen witnesses are built by the existing object numeral/omega certificates. -/
theorem parameters_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (free : FreeVarId → M.Carrier .set) :
    ∃ bound : Fin 13 → M.Carrier .set,
      Project.Formula.satisfies (⟨bound, free⟩ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) conditions := by
  obtain ⟨w, hw⟩ := omega_exists hM
  obtain ⟨n0, _, h0⟩ := numeral_exists hM 0 hw
  obtain ⟨n1, _, h1⟩ := numeral_exists hM 1 hw
  obtain ⟨n2, _, h2⟩ := numeral_exists hM 2 hw
  obtain ⟨n3, _, h3⟩ := numeral_exists hM 3 hw
  obtain ⟨n4, _, h4⟩ := numeral_exists hM 4 hw
  obtain ⟨n5, _, h5⟩ := numeral_exists hM 5 hw
  obtain ⟨n6, _, h6⟩ := numeral_exists hM 6 hw
  obtain ⟨n7, _, h7⟩ := numeral_exists hM 7 hw
  obtain ⟨n8, _, h8⟩ := numeral_exists hM 8 hw
  let v : Fin 13 → M.Carrier .set := Fin.cases n0 (Fin.cases n1 (Fin.cases n0 (Fin.cases n0 (Fin.cases n1 (Fin.cases n2 (Fin.cases n3 (Fin.cases n4 (Fin.cases n5 (Fin.cases n6 (Fin.cases n7 (Fin.cases n8 (Fin.cases w (Fin.elim0)))))))))))))
  have hNumbers : ∀ i : Fin 12,
      numeralValue (Project.FirstOrderSemantics.reduct M).mem (slotCode i) (v i.castSucc) := by
    exact Fin.cases h0 (Fin.cases h1 (Fin.cases h0 (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (Fin.cases h7 (Fin.cases h8 (fun i => Fin.elim0 i))))))))))))
  refine ⟨fun i => v i.rev, (conditions_semantics hM _).mpr ⟨?_, ?_⟩⟩
  · intro i
    simpa only [Fin.rev_rev] using hNumbers i
  · exact hw

/-- The canonical tuple is unique; its omega coordinate is fully internal. -/
theorem parameters_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (free : FreeVarId → M.Carrier .set) {first second : Fin 13 → M.Carrier .set}
    (hFirst : Project.Formula.satisfies (⟨first, free⟩ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) conditions)
    (hSecond : Project.Formula.satisfies (⟨second, free⟩ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) conditions) :
    first = second := by
  have hF := (conditions_semantics hM _).mp hFirst
  have hS := (conditions_semantics hM _).mp hSecond
  have he : ∀ i : Fin 13, first i.rev = second i.rev := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact omega_unique hM hF.2 hS.2
    · exact numeral_unique hM (slotCode j) (hF.1 j) (hS.1 j)
  funext i
  simpa only [Fin.rev_rev] using he i.rev

/-- The actual empty-slot premise of the original history theorem is now discharged. -/
theorem conditions_empty (hM : FirstOrder.Theory.Models M nativeZF)
    {env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13}
    (h : Project.Formula.satisfies env conditions) :
    ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z (env.bound 10) := by
  have hz := ((conditions_semantics hM env).mp h).1 (2 : Fin 12)
  simp only [slotCode, numeralValue, SyntaxNumeralSyntax.numeral, OmegaSyntax.empty,
    Source.Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc] at hz
  have he : (Fin.castSucc (2 : Fin 12)).rev = (10 : Fin 13) := by decide +kernel
  rw [he] at hz
  exact hz

/-- Keep the canonical parameters in the thirteen new bound slots. -/
def parameterEmbedding (i : Fin 13) : Fin 15 := i.castSucc.castSucc

def parameterTerms : Definitional.TermVector 13 15 :=
  (Definitional.TermVector.boundParameters 13 0).rename parameterEmbedding

def parameterBlock : Project.Formula 1 15 :=
  .conj (conditions.rename parameterEmbedding)
    (Project.Formula.related ConstructibleHistory.stageSchema parameterTerms (.bound 14) (.bound 13))

theorem parameterBlock_closed : parameterBlock.FreeClosed := by
  simp -implicitDefEqProofs [parameterBlock, Definitional.Formula.FreeClosed, conditions_closed, parameterTerms]

def canonicalStage : Project.BinarySchema 0 where
  body := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (parameterBlock)))))))))))))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact parameterBlock_closed

theorem parameterBlock_semantics {N : SetTheory.Structure.{u}} (env : SetTheory.Env N 15) :
    Project.Formula.satisfies env parameterBlock ↔
      Project.Formula.satisfies (env.reindex parameterEmbedding) conditions ∧
      ConstructibleHistory.stageSchema.denote (env.reindex parameterEmbedding) (env.bound 14) (env.bound 13) := by
  have he : parameterTerms.evalEnv env = env.reindex parameterEmbedding := by
    rw [SetTheory.Env.mk.injEq]
    constructor
    · funext i
      simp only [parameterTerms, Definitional.TermVector.evalEnv, Definitional.TermVector.eval,
        Definitional.TermVector.rename, Definitional.TermVector.get_bind, Definitional.TermVector.boundParameters,
        Definitional.TermVector.get_ofFn, Definitional.Term.bind, Definitional.Term.eval,
        SetTheory.Env.reindex, Function.comp_apply, Nat.add_zero]
    · rfl
  simp only [parameterBlock, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_rename,
    Project.Formula.satisfies_related_iff, he, Project.Term.eval_bound]

/-- The only hidden witnesses are the thirteen canonical internal sets. -/
theorem canonicalStage_semantics {N : SetTheory.Structure.{u}}
    (env : SetTheory.Env N 0) (index stage : N.Domain) :
    canonicalStage.denote env index stage ↔
      ∃ bound : Fin 13 → N.Domain,
        Project.Formula.satisfies (⟨bound, env.free⟩ : SetTheory.Env N 13) conditions ∧
        ConstructibleHistory.stageSchema.denote ⟨bound, env.free⟩ index stage := by
  unfold canonicalStage Project.BinarySchema.denote
  simp only [Project.Formula.satisfies_exists_iff]
  constructor
  · rintro ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, h⟩
    let rho : SetTheory.Env N 15 := ((((((((((((((env.push index).push stage).push p0).push p1).push p2).push p3).push p4).push p5).push p6).push p7).push p8).push p9).push p10).push p11).push p12
    have hc := (parameterBlock_semantics rho).mp h
    refine ⟨(rho.reindex parameterEmbedding).bound, hc.1, ?_⟩
    exact hc.2
  · rintro ⟨bound, hc, hs⟩
    refine ⟨(bound 12), (bound 11), (bound 10), (bound 9), (bound 8), (bound 7), (bound 6), (bound 5), (bound 4), (bound 3), (bound 2), (bound 1), (bound 0), ?_⟩
    let rho : SetTheory.Env N 15 := ((((((((((((((env.push index).push stage).push (bound 12)).push (bound 11)).push (bound 10)).push (bound 9)).push (bound 8)).push (bound 7)).push (bound 6)).push (bound 5)).push (bound 4)).push (bound 3)).push (bound 2)).push (bound 1)).push (bound 0)
    apply (parameterBlock_semantics rho).mpr
    have he : rho.reindex parameterEmbedding = (⟨bound, env.free⟩ : SetTheory.Env N 13) := by
      rw [SetTheory.Env.mk.injEq]
      constructor
      · funext i
        refine Fin.cases ?_ (fun j0 => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun j1 => ?_) j0
          · rfl
          · refine Fin.cases ?_ (fun j2 => ?_) j1
            · rfl
            · refine Fin.cases ?_ (fun j3 => ?_) j2
              · rfl
              · refine Fin.cases ?_ (fun j4 => ?_) j3
                · rfl
                · refine Fin.cases ?_ (fun j5 => ?_) j4
                  · rfl
                  · refine Fin.cases ?_ (fun j6 => ?_) j5
                    · rfl
                    · refine Fin.cases ?_ (fun j7 => ?_) j6
                      · rfl
                      · refine Fin.cases ?_ (fun j8 => ?_) j7
                        · rfl
                        · refine Fin.cases ?_ (fun j9 => ?_) j8
                          · rfl
                          · refine Fin.cases ?_ (fun j10 => ?_) j9
                            · rfl
                            · refine Fin.cases ?_ (fun j11 => ?_) j10
                              · rfl
                              · refine Fin.cases ?_ (fun j12 => ?_) j11
                                · rfl
                                · exact Fin.elim0 j12
      · rfl
    rw [he]
    exact ⟨hc, hs⟩

/-- Parameter elimination preserves the original stage relation and its unique values. -/
theorem canonicalStage_total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnOrdinals (canonicalStage.denote env) := by
  obtain ⟨bound, hConditions⟩ := parameters_exists hM env.free
  let rho : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13 := ⟨bound, env.free⟩
  have hEmpty := conditions_empty hM hConditions
  intro index hIndex
  obtain ⟨stage, hStage, hUnique⟩ := ConstructibleHistory.stage_total_unique hM rho hEmpty index hIndex
  refine ⟨stage, (canonicalStage_semantics env index stage).mpr ⟨bound, hConditions, hStage⟩, ?_⟩
  intro other hOther
  obtain ⟨otherBound, hOtherConditions, hOtherStage⟩ := (canonicalStage_semantics env index other).mp hOther
  have he := parameters_unique hM env.free hOtherConditions hConditions
  subst otherBound
  exact hUnique other hOtherStage

def uniqueSentence : Project.Sentence where
  formula := Project.Formula.isClassFunctionOnOrdinals canonicalStage Definitional.TermVector.empty
  freeClosed := by simp -implicitDefEqProofs

theorem unique_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence uniqueSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) uniqueSentence]
  intro free
  apply (Project.Formula.satisfies_isClassFunctionOnOrdinals_iff (ModelTransfer.extensionality hM) _ _ _).mpr
  exact canonicalStage_total_unique hM _

theorem unique_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence uniqueSentence) :=
  ModelTransfer.derives (fun _ hM => unique_models hM)

/-- Pure parameter-free candidate constructible domain, using the literal original history. -/
def domain : Project.UnarySchema 0 where
  body := .existsE (.conj (Project.Formula.isOrdinal Project.Term.newest)
    (.existsE (.conj (Project.Formula.related canonicalStage Definitional.TermVector.empty (.bound 1) Project.Term.newest)
      (.mem (.bound 2) Project.Term.newest))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem domain_semantics
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) (x : M.Carrier .set) :
    domain.denote env x ↔ ∃ index, (Project.FirstOrderSemantics.reduct M).IsOrdinal index ∧
      ∃ stage, canonicalStage.denote env index stage ∧ (Project.FirstOrderSemantics.reduct M).mem x stage := by
  -- Membership, rather than equality with a stage, is the constructible-domain endpoint.
  unfold domain Project.UnarySchema.denote

  simp only [Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinal_iff, Project.Formula.satisfies_related_iff,
    Project.Formula.satisfies_mem_iff, Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push, Project.Term.eval_bound_two_push, Definitional.Term.eval_newest]
  have he (index stage : M.Carrier .set) : Definitional.TermVector.empty.evalEnv
      (((env.push x).push index).push stage) = env := by
    rw [SetTheory.Env.mk.injEq]
    constructor
    · funext i
      exact Fin.elim0 i
    · rfl
  simp only [he]

end PPAC.Migration.ConstructibleParameters
