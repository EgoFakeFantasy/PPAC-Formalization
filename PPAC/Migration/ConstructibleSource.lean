/- SAME completed internal L at the source-language Relativization interface.
Reuse existing ProjectDecode, normalization derivations, original soundness,
actual L model, and source/native ZF replay. No new syntax/Sat/kernel backend. -/
import PPAC.Migration.ConstructibleGround
import PPAC.Migration.GodelDefRecursion
import PPAC.Migration.ChoiceNativeBridge

namespace PPAC.Migration.ConstructibleSource
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def domain : Source.Formula 1 := ProjectDecode.reverse (InnerModel.l_m (.bound 0))
  (by simp -implicitDefEqProofs)

/-- Existing open-formula normalization certificate evaluated at ONE parameter;
no second normalization or satisfaction implementation is introduced. -/
theorem domain_correct (hM : FirstOrder.Theory.Models M nativeZF) (x : M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (fun _ => x) domain ↔
      InnerModel.L_d (M := Project.FirstOrderSemantics.reduct M) x := by
  let raw : Project.Formula 1 1 := InnerModel.l_m (.bound 0)
  have hc : raw.FreeClosed := by simp -implicitDefEqProofs [raw]
  let q := Project.fo_formula raw hc
  let bs : FirstOrder.VariableSubstitution ℒ [SetSort.set] [] [SetSort.set] :=
    fun v => match v with | .here => .fvar .here | .there p => nomatch p
  let ef := (FirstOrder.Env.empty (M := M)).pushFree x
  let eb := (FirstOrder.Env.empty (M := M)).pushBound x
  have he : ef.pullback (FirstOrder.Substitution.map bs FirstOrder.VariableSubstitution.empty) = eb := by
    apply FirstOrder.Env.ext
    · intro sort v
      cases v with
      | here => rfl
      | there v => nomatch v
    · intro sort v
      nomatch v
  have hn := Normalization.equivalent_substitute q bs FirstOrder.VariableSubstitution.empty nativeZF []
  have ht := hn.sound hM ef (by intro f hf; cases hf)
  change (q.substituteMapped bs FirstOrder.VariableSubstitution.empty).satisfies ef ↔
    ((Normalization.formula q).substituteMapped bs FirstOrder.VariableSubstitution.empty).satisfies ef at ht
  have hq := FirstOrder.Formula.satisfies_substitute ef (FirstOrder.Substitution.map bs FirstOrder.VariableSubstitution.empty) q
  have hqn := FirstOrder.Formula.satisfies_substitute ef (FirstOrder.Substitution.map bs FirstOrder.VariableSubstitution.empty) (Normalization.formula q)
  rw [he] at hq hqn
  have norm : q.satisfies eb ↔ (Normalization.formula q).satisfies eb := hq.symm.trans (ht.trans hqn)
  let τ : Fin 1 → FirstOrder.Variable (Project.fo_bound_context 1) SetSort.set :=
    fun i => Project.fo_bound_variable (Fin.rev i)
  have back := ProjectDecode.fo_formula Fin.rev τ (fun i => by simp only [τ,Fin.rev_rev]) raw hc
  have decoded := Translation.realizes_formula M τ eb domain
  change (Translation.formula τ (ProjectDecode.formula Fin.rev raw hc)).satisfies eb ↔ _ at decoded
  rw [back] at decoded
  have decoded' : (Normalization.formula q).satisfies eb ↔
      Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (fun _ => x) domain := by
    have hev : (fun i : Fin 1 => eb.boundVal (τ i)) = (fun _ => x) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hev] at decoded
    exact decoded
  have hp := Project.FirstOrderSemantics.formula_correct (ModelTransfer.extensionality hM) raw hc eb (fun _ => x)
  have hl := InnerModel.l_sat_l (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))
    (Project.FirstOrderSemantics.projectEnv (depth := 1) eb (fun _ => x)) (.bound 0)
  exact decoded'.symm.trans (norm.symm.trans (hp.trans hl))

attribute [local irreducible] domain

/-- Only repack the SAME native internal L into the existing pure signature. -/
def model (hM : FirstOrder.Theory.Models M nativeZF) : FirstOrder.Structure.{0,0,0,u} ℒ where
  Carrier := fun _ => (InnerModel.l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM))).Domain
  nonempty := fun _ => (InnerModel.l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM))).nonempty
  funcInterp := fun f => nomatch f
  relInterp := fun relation values =>
    match relation, values with
    | .membership, .cons x (.cons y .nil) =>
      (InnerModel.l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM))).mem x y

theorem model_zf (hM : FirstOrder.Theory.Models M nativeZF) : FirstOrder.Theory.Models (model hM) nativeZF :=
  ModelTransfer.project_models_iff.mpr (InnerModel.l_model_zf_l (ModelTransfer.project_models_iff.mp hM))

theorem model_choice (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence Axioms.choice).TrueIn (model hM) := by
  have hL := InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hM)
  exact (Project.FirstOrderSemantics.sentence_correct (ℳ := model hM) hL.1 Axioms.choice).mpr (hL.2 _ .choice)

theorem model_zfc (hM : FirstOrder.Theory.Models M nativeZF) :
    FirstOrder.Theory.Models (model hM) (Project.fo_theory SetTheory.ZFC) := by
  have hL := InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hM)
  exact (Project.FirstOrderSemantics.models_iff (ℳ := model hM) hL.1 SetTheory.ZFC).mpr hL

theorem domain_at (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (v : Fin n → M.Carrier .set) (x : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (Relativization.domain domain x) ↔
      InnerModel.L_d (M := Project.FirstOrderSemantics.reduct M) (v x) :=
  (DefinableMinimaChoice.realize_rename _ domain (fun _ => x) v).trans (domain_correct hM (v x))

/-- Reuse the SOURCE relative AST with its LAST-variable binder; the target
is the SAME actual L structure already supplied by the donor. -/
theorem relative_realize (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Source.Formula n) (v : Fin n → (model hM).Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (fun i => (v i).val)
      (Relativization.formula domain p) ↔
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct (model hM)).mem v p := by
  have val_last {k} (v : Fin k → (model hM).Carrier .set) (x : (model hM).Carrier .set) :
      (fun i : Fin (k+1) => ((Fin.lastCases x v i : (model hM).Carrier .set)).val) = Fin.lastCases x.val (fun i => (v i).val) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  induction p with
  | bot => rfl
  | mem => rfl
  | equal x y => exact ⟨Subtype.ext,congrArg Subtype.val⟩
  | imp p q ih jh | conj p q ih jh | disj p q ih jh =>
    simp only [Relativization.formula,Source.Formula.Realize,ih,jh]
  | @all n p ih =>
    change (∀ x, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (fun i => (v i).val)) (Relativization.domain domain (Fin.last n)) →
      Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (fun i => (v i).val)) (Relativization.formula domain p)) ↔ _
    simp only [domain_at hM,Fin.lastCases_last]
    constructor
    · intro h x
      have ht := ih (Fin.lastCases x v)
      rw [val_last v x] at ht
      exact ht.mp (h x.val x.property)
    · intro h x hx
      have ht := ih (Fin.lastCases ⟨x,hx⟩ v)
      rw [val_last v (⟨x,hx⟩ : (model hM).Carrier .set)] at ht
      exact ht.mpr (h ⟨x,hx⟩)
  | @ex n p ih =>
    change (∃ x, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (fun i => (v i).val)) (Relativization.domain domain (Fin.last n)) ∧
      Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (fun i => (v i).val)) (Relativization.formula domain p)) ↔ _
    simp only [domain_at hM,Fin.lastCases_last]
    constructor
    · rintro ⟨x,hx,h⟩
      have ht := ih (Fin.lastCases ⟨x,hx⟩ v)
      rw [val_last v (⟨x,hx⟩ : (model hM).Carrier .set)] at ht
      exact ⟨⟨x,hx⟩,ht.mp h⟩
    · rintro ⟨x,h⟩
      have ht := ih (Fin.lastCases x v)
      rw [val_last v x] at ht
      exact ⟨x.val,x.property,ht.mpr h⟩

theorem relative_sentence_models (hM : FirstOrder.Theory.Models M nativeZF) (p : Source.Sentence)
    (hp : (Translation.sentence p).TrueIn (model hM)) :
    (Translation.sentence (Relativization.formula domain p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  have h := (relative_realize hM p Fin.elim0).mpr ((Translation.realizes_sentence (model hM) p).mp hp)
  have he : (fun i : Fin 0 => ((Fin.elim0 i : (model hM).Carrier .set)).val) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he] at h
  exact h

/-- ALL original source axioms, including arbitrary Separation/Replacement. -/
theorem zf_axiom_kernel {p : Source.Sentence} (hp : Source.SetLanguage.ZF p) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Relativization.formula domain p)) := by
  apply ModelTransfer.derives
  intro M hM
  exact relative_sentence_models hM p ((ZFReplay.replay_axiom hp).semantically_entails (model hM) (model_zf hM))

theorem choice_kernel : FirstOrder.Derives nativeZF []
    (Translation.sentence (Relativization.formula domain Source.SetLanguage.AC)) := by
  apply ModelTransfer.derives
  intro M hM
  have hc := ChoiceNativeBridge.native_reverse.semantically_entails (model hM) (model_zf hM)
  exact relative_sentence_models hM _ (hc (model_choice hM))

theorem nonempty_kernel : FirstOrder.Derives nativeZF [] (Translation.sentence (.ex domain)) := by
  apply ModelTransfer.derives
  intro M hM
  apply (Translation.realizes_sentence M (.ex domain)).mpr
  change ∃ x, Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x Fin.elim0) domain
  obtain ⟨a⟩ := (model hM).nonempty .set
  refine ⟨a.val,?_⟩
  have he : (Fin.lastCases a.val Fin.elim0 : Fin 1 → M.Carrier .set) = (fun _ => a.val) := by
    funext i
    exact Fin.lastCases rfl (fun j => Fin.elim0 j) i
  rw [he]
  exact (domain_correct hM a.val).mpr a.property

/-- Discharge the ACTUAL interpreted theory consumed by existing InterpretedZF. -/
theorem replay {free : Syntax.Ctx} {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives (TheoryTransport.theory (Relativization.theory domain Source.SetLanguage.ZF)) Γ p) :
    FirstOrder.Derives nativeZF Γ p := by
  apply FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s,⟨p,hp,rfl⟩,rfl⟩
  exact zf_axiom_kernel hp

theorem native_sentence {p : FirstOrder.Sentence ℒ} (h : FirstOrder.Derives nativeZF [] p) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula domain (Reverse.sentence p))) :=
  FirstOrder.Derives.imp_elim (replay (InterpretedZF.native_sentence domain h)) nonempty_kernel

theorem source_sentence {p : Source.Sentence}
    (h : FirstOrder.Derives nativeZF [] (Translation.sentence p)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Relativization.formula domain p)) :=
  FirstOrder.Derives.imp_elim (replay (InterpretedZF.source_sentence domain h)) nonempty_kernel

theorem collection_kernel {n : Nat} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula domain (CollectionSyntax.collection p))) :=
  FirstOrder.Derives.imp_elim (replay (InterpretedZF.collection domain p)) nonempty_kernel

/-- Any actually supplied native ZFC proof of a SOURCE sentence transfers
through the SAME L domain; not just a list of fixed axiom examples. -/
theorem source_zfc_sentence {p : Source.Sentence}
    (h : FirstOrder.Derives (Project.fo_theory SetTheory.ZFC) [] (Translation.sentence p)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Relativization.formula domain p)) := by
  apply ModelTransfer.derives
  intro M hM
  exact relative_sentence_models hM p (h.semantically_entails (model hM) (model_zfc hM))

end PPAC.Migration.ConstructibleSource
