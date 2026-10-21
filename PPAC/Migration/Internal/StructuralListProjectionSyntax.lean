import PPAC.Migration.Internal.ObjectStructuralListLength

/-! 两个外部布尔实例只选择head或tail；每个实例均为纯对象关系。 -/
namespace PPAC.Migration.Internal.StructuralListProjectionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax

def body {m} (head : Bool) (w x y a : Fin m) : Formula m :=
  ((Formula.mem y w).conj (.mem a w)).conj (consCode w (if head then y else a) (if head then a else y) x)

def selected {m} (head : Bool) (w x y : Fin m) : Formula m := .ex (body head w.castSucc x.castSucc y.castSucc (Fin.last m))

def hasCons {m} (head : Bool) (w x : Fin m) : Formula m := .ex (selected head w.castSucc x.castSucc (Fin.last m))

def step {m} (head : Bool) (w x y : Fin m) : Formula m :=
  (selected head w x y).disj ((hasCons head w x).neg.conj (empty y))

def hasStep {m} (head : Bool) (w x : Fin m) : Formula m := .ex (step head w.castSucc x.castSucc (Fin.last m))

def matrix (head : Bool) : Formula 3 := step head 0 1 2

theorem body_rename {m k} (head : Bool) (w x y a : Fin m) (r : Fin m → Fin k) :
    (body head w x y a).rename r = body head (r w) (r x) (r y) (r a) := by
  cases head <;> simp only [body, Bool.false_eq_true, if_false, if_true, Formula.rename, consCode_rename]

theorem selected_rename {m k} (head : Bool) (w x y : Fin m) (r : Fin m → Fin k) :
    (selected head w x y).rename r = selected head (r w) (r x) (r y) := by
  simp only [selected, Formula.rename, body_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasCons_rename {m k} (head : Bool) (w x : Fin m) (r : Fin m → Fin k) :
    (hasCons head w x).rename r = hasCons head (r w) (r x) := by
  simp only [hasCons, Formula.rename, selected_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem step_rename {m k} (head : Bool) (w x y : Fin m) (r : Fin m → Fin k) :
    (step head w x y).rename r = step head (r w) (r x) (r y) := by
  simp only [step, Formula.rename, Formula.neg, selected_rename, hasCons_rename, empty_rename]

theorem hasStep_rename {m k} (head : Bool) (w x : Fin m) (r : Fin m → Fin k) :
    (hasStep head w x).rename r = hasStep head (r w) (r x) := by
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

theorem intro_selected {m} {Γ : Context m} (head : Bool) (w x y a : Fin m)
    (hb : Derives Γ (body head w x y a)) : Derives Γ (selected head w x y) := by
  apply Derives.exI a
  simpa only [Formula.instantiate, body_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb

theorem intro_hasCons {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hy : Derives Γ (selected head w x y)) : Derives Γ (hasCons head w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem intro_value {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hy : Derives Γ (step head w x y)) : Derives Γ (hasStep head w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

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
end PPAC.Migration.Internal.StructuralListProjectionSyntax
