/- Pinned ForcingNames.Name.HS.smul -> SymmetricNames.forces_symmetry.
Literal stabilizer conjugacy and normality supply the symmetry step; original
Child induction supplies hereditary closure. Both action directions then
instantiate the existing full formula theorem with the actual HS predicate. -/
import PPAC.Migration.ForcingHS
import PPAC.Migration.ForcingStabilizerTransport
import PPAC.Migration.ForcingFormulaSymmetry

namespace PPAC.Migration.ForcingHSAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingStabilizer (Action action)
open ForcingStabilizerTransport (Context context)
open ForcingHS (HS hs)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preservesAt {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F r sigma : Fin m) : Formula m :=
  (hs A rho G P F sigma).imp (.all ((action P.castSucc r.castSucc sigma.castSucc (Fin.last m)).imp
    (hs A (paramsUp rho) G.castSucc P.castSucc F.castSucc (Fin.last m))))

theorem preservesAt_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P F r sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (preservesAt A rho G P F r sigma) ↔
      (HS A (fun j => env (rho j)) (env G) (env P) (env F) (env sigma) →
        ∀ out, Action (env P) (env r) (env sigma) out → HS A (fun j => env (rho j)) (env G) (env P) (env F) out) := by
  simp only [preservesAt,Formula.Realize,ForcingHS.hs_semantics (M := M),ForcingStabilizer.action_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Exact source Child induction; no HS-closure hypothesis is used. -/
theorem hs_action (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P F c r i : M.Carrier .set}
    (hc : Context A params G P F c r i) :
    ∀ sigma, HS A params G P F sigma → ∀ out, Action P r sigma out → HS A params G P F out := by
  have hr := hc.2.2.1
  let inputs : Fin (k+4) → M.Carrier .set := Fin.lastCases r (Fin.lastCases F (Fin.lastCases P (Fin.lastCases G params)))
  let matrix := preservesAt A (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
    (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hm : ∀ sigma, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases sigma inputs) matrix ↔
      (HS A params G P F sigma → ∀ out, Action P r sigma out → HS A params G P F out) := by
    intro sigma
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      preservesAt_semantics (M := M) (Fin.lastCases sigma inputs) A (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
        (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hall := ForcingMapLaws.formula_induction hM matrix inputs (by
    intro sigma ih
    apply (hm sigma).mpr
    intro hHS out ha
    have hn := ForcingHS.isName hHS
    apply ForcingHS.intro_hs hM A params G P F out (ForcingNameConjugacy.name_preservation hM hr.1 hn ha)
      (ForcingStabilizerTransport.symmetric_transport hM hc hn ha (ForcingHS.symmetric_of_hs hHS))
    intro child condition he
    obtain ⟨tau,p,hedge,hchild,_⟩ := (ForcingMapConditions.edge_mapping hM
      (ForcingConditionAction.act_function (args2 P r) (0 : Fin 2) 1 hr.1) ha child condition).mp he
    exact (hm tau).mp (ih tau p hedge) (ForcingHS.child hHS hedge) child hchild)
  intro sigma
  exact (hm sigma).mp (hall sigma)

def sentence {k : Nat} (A : Formula (k+2)) (G P F c r i sigma : Fin k) : Source.Sentence :=
  ((context A id G P F c r i).imp (preservesAt A id G P F r sigma)).close

theorem models {k : Nat} (A : Formula (k+2)) (G P F c r i sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence A G P F c r i sigma)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hc
  exact (preservesAt_semantics (M := M) env A id G P F r sigma).mpr
    (hs_action hM ((ForcingStabilizerTransport.context_semantics (M := M) env A id G P F c r i).mp hc) (env sigma))

theorem kernel_certificate {k : Nat} (A : Formula (k+2)) (G P F c r i sigma : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence A G P F c r i sigma)) :=
  ModelTransfer.derives (fun _ hM => models A G P F c r i sigma hM)

/-- Discharge the two name-domain obligations for actual HS, using both source
normal-filter conjugations and the already constructed inverse name action. -/
theorem domain_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F c d r i : Fin k)
    (hf : Context A params (params G) (params P) (params F) (params c) (params r) (params i))
    (hb : Context A params (params G) (params P) (params F) (params d) (params i) (params r)) :
    ForcingFormulaSymmetry.DomainTransport (ForcingConditionAction.actFormula P r) (ForcingHS.predicate A G P F) params := by
  constructor
  · intro x hx
    have hxHS := (ForcingHS.predicate_semantics (M := M) A G P F params x).mp hx
    obtain ⟨y,hy⟩ := ForcingNameConjugacy.exists_action hM hf.2.2.1.1 x
    exact ⟨y,(ForcingHS.predicate_semantics (M := M) A G P F params y).mpr (hs_action hM hf x hxHS y hy),
      (ForcingNameConjugacy.action_iff params P r x y).mpr hy⟩
  · intro y hy
    have hyHS := (ForcingHS.predicate_semantics (M := M) A G P F params y).mp hy
    obtain ⟨x,hx⟩ := ForcingNameConjugacy.exists_action hM hb.2.2.1.1 y
    have hxHS := hs_action hM hb y hyHS x hx
    have hback := ForcingNameConjugacy.inverse_action hM hb.2.2.1.1 hb.2.2.2.1 hb.2.2.2.2.1
      (ForcingHS.isName hyHS) hx
    exact ⟨x,(ForcingHS.predicate_semantics (M := M) A G P F params x).mpr hxHS,
      (ForcingNameConjugacy.action_iff params P r x y).mpr hback⟩

/-- The original full formula symmetry now uses the actual HS domain; no
arbitrary H-domain closure or surjectivity premise remains in this sentence. -/
def formulaSentence {k n : Nat} (A R : Formula (k+2)) (v w : Fin n → Fin k)
    (G P F c d r i p p' : Fin k) (phi : Formula n) : Source.Sentence :=
  ((context A id G P F c r i).imp ((context A id G P F d i r).imp
    ((ForcingAtomicSymmetry.orderOn R P r).imp
      (ForcingFormulaSymmetry.conclusion (ForcingConditionAction.actFormula P r) R
        (ForcingHS.predicate A G P F) v w P p p' phi)))).close

theorem formula_models {k n : Nat} (A R : Formula (k+2)) (v w : Fin n → Fin k)
    (G P F c d r i p p' : Fin k) (phi : Formula n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (formulaSentence A R v w G P F c d r i p p' phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf hb ho
  have hf' := (ForcingStabilizerTransport.context_semantics (M := M) env A id G P F c r i).mp hf
  have hb' := (ForcingStabilizerTransport.context_semantics (M := M) env A id G P F d i r).mp hb
  exact ForcingFormulaSymmetry.conclusion_models hM (ForcingConditionAction.actFormula P r) R
    (ForcingHS.predicate A G P F) v w P p p' phi env
    (ForcingAtomicSymmetry.action_transport R env P r hf'.2.2.1
      ((ForcingAtomicSymmetry.orderOn_semantics (M := M) env R P r).mp ho))
    (domain_transport hM A env G P F c d r i hf' hb')

theorem formula_kernel_certificate {k n : Nat} (A R : Formula (k+2)) (v w : Fin n → Fin k)
    (G P F c d r i p p' : Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (formulaSentence A R v w G P F c d r i p p' phi)) :=
  ModelTransfer.derives (fun _ hM => formula_models A R v w G P F c d r i p p' phi hM)

end PPAC.Migration.ForcingHSAction
