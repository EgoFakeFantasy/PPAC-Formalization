/- Reuse the completed arbitrary-model Jensen L theorem on the PINNED
native base. Every relative sentence is an ACTUAL object formula and every
kernel result is FirstOrder.Derives nativeZF [], not external consistency.
No object Choice/standardness/well-foundedness/universe enlargement assumed. -/
import PPAC.Companion.YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Choice
import PPAC.Migration.InterpretedZF

namespace PPAC.Migration.ConstructibleGround
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Existing complete relative formula, retaining arbitrary schema indices. -/
def relative (p : Project.Sentence) : Project.Sentence where
  formula := InnerModel.l_rel_m p.formula
  freeClosed := InnerModel.l_rel_closed_l p.formula p.freeClosed

/-- All models, same universe, actual internal L, full original semantics. -/
theorem relative_models (hM : FirstOrder.Theory.Models M nativeZF) (p : Project.Sentence)
    (hp : (InnerModel.l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM))).SatisfiesSentence p) :
    (Project.fo_sentence (relative p)).TrueIn M := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let hKPi := ZF.models_kpi_l hZF
  let L := InnerModel.l_model_l hKPi
  let a : L.Domain := Classical.choice L.nonempty
  let ρ : SetTheory.Env L 0 := ⟨Fin.elim0,fun _ => a⟩
  have hpl : Project.Formula.satisfies ρ p.formula :=
    (Structure.satisfiesSentence_iff L p).mp hp ρ.free
  have hrel := (InnerModel.l_rel_sat_l hKPi p.formula ρ).mp hpl
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (relative p)]
  intro free
  exact (Project.Formula.closed_env_l _ (InnerModel.l_rel_closed_l p.formula p.freeClosed)
    (funext fun i => Fin.elim0 i)).mp hrel

/-- Every original ZFC axiom, including unrestricted Separation/Collection. -/
theorem zfc_axiom_kernel {p : Project.Sentence} (hp : SetTheory.ZFC p) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (relative p)) := by
  apply ModelTransfer.derives
  intro M hM
  exact relative_models hM p ((InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hM)).2 p hp)

theorem zf_axiom_kernel {p : Project.Sentence} (hp : SetTheory.ZF p) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (relative p)) :=
  zfc_axiom_kernel (.zf hp)

theorem choice_kernel : FirstOrder.Derives nativeZF [] (Project.fo_sentence (relative Axioms.choice)) :=
  zfc_axiom_kernel .choice

/-- Existing definable set-like global order INSIDE the SAME actual L. -/
theorem global_order_kernel : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (relative InnerModel.js_universe_s)) := by
  apply ModelTransfer.derives
  intro M hM
  exact relative_models hM _ (InnerModel.js_l_model_l (ZF.models_kpi_l (ModelTransfer.project_models_iff.mp hM)))

def nonemptySentence : Project.Sentence where
  formula := .existsE (InnerModel.l_m .newest)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem nonempty_kernel : FirstOrder.Derives nativeZF [] (Project.fo_sentence nonemptySentence) := by
  apply ModelTransfer.derives
  intro M hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  let L := InnerModel.l_model_l (ZF.models_kpi_l hZF)
  obtain ⟨a⟩ := L.nonempty
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) nonemptySentence]
  intro free
  change Project.Formula.satisfies
    ({ bound := Fin.elim0, free := free } : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0)
    (.existsE (InnerModel.l_m .newest))
  simp only [Project.Formula.satisfies_exists_iff,
    InnerModel.l_sat_l (ZF.modelsKP hZF),Definitional.Term.eval_newest]
  exact ⟨a.val,a.property⟩

end PPAC.Migration.ConstructibleGround
