/- Literal stabilizers for pinned ForcingNames.ConditionAction.Name.Symmetric.
A represents the source action family g -> a condition permutation graph.
No symmetric-name or forcing conclusion is supplied as an input predicate. -/
import PPAC.Migration.ForcingConditionAction

namespace PPAC.Migration.ForcingStabilizer
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel Mapped)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reuse the actual name action of the condition graph, with two local parameters. -/
def action {m : Nat} (P r sigma out : Fin m) : Formula m :=
  ForcingMapConditions.mapping (ForcingConditionAction.actFormula (0 : Fin 2) 1) (args2 P r) sigma out

def Action (P r sigma out : M.Carrier .set) : Prop :=
  Mapped (ForcingConditionAction.actFormula (0 : Fin 2) 1) (args2 P r) sigma out

theorem action_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P r sigma out : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (action P r sigma out) ↔
      Action (env P) (env r) (env sigma) (env out) := by
  have he : (fun i => env (args2 P r i)) = args2 (env P) (env r) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun z => Fin.elim0 z) j
      rfl
  simpa only [action,Action,he] using
    ForcingMapConditions.mapping_semantics (M := M) env (ForcingConditionAction.actFormula (0 : Fin 2) 1)
      (args2 P r) sigma out

def fixed {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (P sigma g : Fin m) : Formula m :=
  .ex ((ReplacementPredicates.rel A (paramsUp rho) g.castSucc (Fin.last m)).conj
    (action P.castSucc (Fin.last m) sigma.castSucc sigma.castSucc))

def Fixed {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (P sigma g : M.Carrier .set) : Prop :=
  ∃ r, MapRel A params g r ∧ Action P r sigma sigma

theorem fixed_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (P sigma g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fixed A rho P sigma g) ↔
      Fixed A (fun i => env (rho i)) (env P) (env sigma) (env g) := by
  simp only [fixed,Fixed,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    action_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- A stabilizer contains exactly the group codes whose literal name action fixes sigma. -/
def stabilizer {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m)
    (G P sigma S : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) S.castSucc).iff ((Formula.mem (Fin.last m) G.castSucc).conj
    (fixed A (paramsUp rho) P.castSucc sigma.castSucc (Fin.last m))))

def Stabilizer {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P sigma S : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g S ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem g G ∧ Fixed A params P sigma g

theorem stabilizer_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (G P sigma S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (stabilizer A rho G P sigma S) ↔
      Stabilizer A (fun i => env (rho i)) (env G) (env P) (env sigma) (env S) := by
  simp only [stabilizer,Stabilizer,Source.Formula.iff,Formula.Realize,fixed_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h g => ⟨(h g).1,(h g).2⟩,fun h g => ⟨(h g).mp,(h g).mpr⟩⟩

theorem exists_stabilizer (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P sigma : M.Carrier .set) :
    ∃ S, Stabilizer A params G P sigma S := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let inputs : Fin (k+2) → M.Carrier .set := Fin.lastCases sigma (Fin.lastCases P params)
  let query := fixed A (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))
  have sep := (GodelDefOutput.separation_semantics E query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨S,hS⟩ := sep inputs G
  refine ⟨S,fun g => (hS g).trans (and_congr Iff.rfl ?_)⟩
  simpa only [query,inputs,E,Fin.lastCases_last,Fin.lastCases_castSucc] using
    fixed_semantics (M := M) (Fin.lastCases g inputs) A (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P sigma S T : M.Carrier .set}
    (hS : Stabilizer A params G P sigma S) (hT : Stabilizer A params G P sigma T) : S = T := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  exact fun g => (hS g).trans (hT g).symm

def symmetric {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m)
    (G P F sigma : Fin m) : Formula m :=
  .ex ((stabilizer A (paramsUp rho) G.castSucc P.castSucc sigma.castSucc (Fin.last m)).conj
    (.mem (Fin.last m) F.castSucc))

def Symmetric {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P F sigma : M.Carrier .set) : Prop :=
  ∃ S, Stabilizer A params G P sigma S ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem S F

theorem symmetric_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (symmetric A rho G P F sigma) ↔
      Symmetric A (fun i => env (rho i)) (env G) (env P) (env F) (env sigma) := by
  simp only [symmetric,Symmetric,Formula.Realize,stabilizer_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Exact membership in the unique constructed stabilizer, not a new symmetry axiom. -/
theorem symmetric_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P F sigma S : M.Carrier .set}
    (hS : Stabilizer A params G P sigma S) :
    Symmetric A params G P F sigma ↔ (Definitional.Project.FirstOrderSemantics.reduct M).mem S F := by
  constructor
  · rintro ⟨T,hT,hTF⟩
    exact unique hM hT hS ▸ hTF
  · intro h
    exact ⟨S,hS,h⟩

theorem empty_symmetric (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P F empty : M.Carrier .set)
    (hAction : ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G →
      ∃ r, MapRel A params g r ∧ ForcingConditionGraphs.Endomap P r)
    (htop : (Definitional.Project.FirstOrderSemantics.reduct M).mem G F)
    (hEmpty : ∀ z, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem z empty) :
    Symmetric A params G P F empty := by
  refine ⟨G,?_,htop⟩
  intro g
  constructor
  · intro hg
    obtain ⟨r,hgr,hr⟩ := hAction g hg
    exact ⟨hg,r,hgr,ForcingMapConditions.empty_mapping hM
      (ForcingConditionAction.act_function (args2 P r) (0 : Fin 2) 1 hr) empty hEmpty⟩
  · exact fun h => h.1

def existenceSentence {k : Nat} (A : Formula (k+2)) (G P sigma : Fin k) : Source.Sentence :=
  (Formula.ex (stabilizer A Fin.castSucc G.castSucc P.castSucc sigma.castSucc (Fin.last k))).close

theorem existence_models {k : Nat} (A : Formula (k+2)) (G P sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence A G P sigma)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨S,hS⟩ := exists_stabilizer hM A env (env G) (env P) (env sigma)
  refine ⟨S,?_⟩
  exact (stabilizer_semantics (M := M) (Fin.lastCases S env) A Fin.castSucc G.castSucc P.castSucc
    sigma.castSucc (Fin.last k)).mpr (by simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hS)

theorem existence_kernel_certificate {k : Nat} (A : Formula (k+2)) (G P sigma : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence A G P sigma)) :=
  ModelTransfer.derives (fun _ hM => existence_models A G P sigma hM)

end PPAC.Migration.ForcingStabilizer
