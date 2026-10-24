import PPAC.Migration.Internal.PairingProjectionNatural
import PPAC.Migration.Internal.NaturalEvaluationStep

/-! 原head/tail：先解任意原始节点的载荷，再解裸配数；不要求规范Cons标签。 -/
namespace PPAC.Migration.Internal.RawCodeProjectionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def body {m} (head : Bool) (w x y p : Fin m) : Formula m :=
  (PairingProjectionSyntax.step true false w x p).conj (PairingProjectionSyntax.step false head w p y)

def step {m} (head : Bool) (w x y : Fin m) : Formula m := .ex (body head w.castSucc x.castSucc y.castSucc (Fin.last m))
def hasStep {m} (head : Bool) (w x : Fin m) : Formula m := .ex (step head w.castSucc x.castSucc (Fin.last m))
def matrix (head : Bool) : Formula 3 := step head 0 1 2

theorem body_rename {m l} (head : Bool) (w x y p : Fin m) (ρ : Fin m → Fin l) :
    (body head w x y p).rename ρ = body head (ρ w) (ρ x) (ρ y) (ρ p) := by
  simp only [body, Formula.rename, PairingProjectionSyntax.step_rename]

theorem step_rename {m l} (head : Bool) (w x y : Fin m) (ρ : Fin m → Fin l) :
    (step head w x y).rename ρ = step head (ρ w) (ρ x) (ρ y) := by
  simp only [step, Formula.rename, body_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasStep_rename {m l} (head : Bool) (w x : Fin m) (ρ : Fin m → Fin l) :
    (hasStep head w x).rename ρ = hasStep head (ρ w) (ρ x) := by
  simp only [hasStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (head : Bool) (ρ : Fin 1 → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel (matrix head) ρ x y = step head (ρ 0) x y := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 3) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 1).castSucc = x
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h2 : Fin.lastCases y (Fin.lastCases x ρ) (2 : Fin 3) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 2) = y
    exact Fin.lastCases_last
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, matrix, step_rename, h0, h1, h2]

theorem intro_step {m} {Γ : Context m} (head : Bool) (w x y p : Fin m)
    (hp : Derives Γ (PairingProjectionSyntax.step true false w x p))
    (hy : Derives Γ (PairingProjectionSyntax.step false head w p y)) : Derives Γ (step head w x y) := by
  have hb : Derives Γ (body head w x y p) := .conjI hp hy
  apply Derives.exI p
  simpa only [Formula.instantiate, body_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb

theorem intro_value {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hy : Derives Γ (step head w x y)) : Derives Γ (hasStep head w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem output_subst {m} {Γ : Context m} (head : Bool) (w x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (step head w x y)) : Derives Γ (step head w x z) := by
  have hi : Derives Γ ((step head w.castSucc x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (step head w.castSucc x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

def params {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def recursors {m} (head : Bool) (w a : Fin m) : Formula m :=
  OrdinalRecursionExistenceSyntax.allUnique (NaturalRecursionSyntax.matrix (matrix head)) (NaturalRecursionSyntax.extend (params w) w a)

def iteration {m} (head : Bool) (w a r y : Fin m) : Formula m :=
  NaturalEvaluationSyntax.evaluation (matrix head) (params w) w a r y

def iterationFiber {m} (head : Bool) (w a r : Fin m) : Formula m :=
  NaturalEvaluationSyntax.uniqueValue (matrix head) (params w) w a r

theorem recursors_rename {m k} (head : Bool) (w a : Fin m) (s : Fin m → Fin k) :
    (recursors head w a).rename s = recursors head (s w) (s a) := by
  simp only [recursors, OrdinalRecursionExistenceSyntax.allUnique_rename, NaturalRecursionSyntax.extend_rename, params]
  rfl

theorem iteration_rename {m k} (head : Bool) (w a r y : Fin m) (s : Fin m → Fin k) :
    (iteration head w a r y).rename s = iteration head (s w) (s a) (s r) (s y) := by
  simp only [iteration, NaturalEvaluationSyntax.evaluation_rename, params]
  rfl

theorem iterationFiber_rename {m k} (head : Bool) (w a r : Fin m) (s : Fin m → Fin k) :
    (iterationFiber head w a r).rename s = iterationFiber head (s w) (s a) (s r) := by
  simp only [iterationFiber, NaturalEvaluationSyntax.uniqueValue_rename, params]
  rfl
end PPAC.Migration.Internal.RawCodeProjectionSyntax
