import PPAC.Migration.Internal.StructuralNodeDecodeUnique

/-! 原裸配数与后继节点的两分量投影；两个布尔仅索引固定外部模式。 -/
namespace PPAC.Migration.Internal.PairingProjectionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def encoded {m} (raw : Bool) (w a b x : Fin m) : Formula m :=
  if raw then StructuralNodeSyntax.raw w a b x else GodelPairSyntax.code w a b x

theorem encoded_rename {m l} (raw : Bool) (w a b x : Fin m) (ρ : Fin m → Fin l) :
    (encoded raw w a b x).rename ρ = encoded raw (ρ w) (ρ a) (ρ b) (ρ x) := by
  cases raw <;> simp only [encoded, Bool.false_eq_true, if_false, if_true, StructuralNodeSyntax.raw_rename, GodelPairSyntax.code_rename]

def body {m} (raw head : Bool) (w x y a : Fin m) : Formula m :=
  ((Formula.mem y w).conj (.mem a w)).conj (encoded raw w (if head then y else a) (if head then a else y) x)

def selected {m} (raw head : Bool) (w x y : Fin m) : Formula m := .ex (body raw head w.castSucc x.castSucc y.castSucc (Fin.last m))

def hasSelected {m} (raw head : Bool) (w x : Fin m) : Formula m := .ex (selected raw head w.castSucc x.castSucc (Fin.last m))

def step {m} (raw head : Bool) (w x y : Fin m) : Formula m :=
  (selected raw head w x y).disj ((hasSelected raw head w x).neg.conj (empty y))

def hasStep {m} (raw head : Bool) (w x : Fin m) : Formula m := .ex (step raw head w.castSucc x.castSucc (Fin.last m))

def matrix (raw head : Bool) : Formula 3 := step raw head 0 1 2

theorem body_rename {m k} (raw head : Bool) (w x y a : Fin m) (r : Fin m → Fin k) :
    (body raw head w x y a).rename r = body raw head (r w) (r x) (r y) (r a) := by
  cases head <;> simp only [body, Bool.false_eq_true, if_false, if_true, Formula.rename, encoded_rename]

theorem selected_rename {m k} (raw head : Bool) (w x y : Fin m) (r : Fin m → Fin k) :
    (selected raw head w x y).rename r = selected raw head (r w) (r x) (r y) := by
  simp only [selected, Formula.rename, body_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasSelected_rename {m k} (raw head : Bool) (w x : Fin m) (r : Fin m → Fin k) :
    (hasSelected raw head w x).rename r = hasSelected raw head (r w) (r x) := by
  simp only [hasSelected, Formula.rename, selected_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem step_rename {m k} (raw head : Bool) (w x y : Fin m) (r : Fin m → Fin k) :
    (step raw head w x y).rename r = step raw head (r w) (r x) (r y) := by
  simp only [step, Formula.rename, Formula.neg, selected_rename, hasSelected_rename, empty_rename]

theorem hasStep_rename {m k} (raw head : Bool) (w x : Fin m) (r : Fin m → Fin k) :
    (hasStep raw head w x).rename r = hasStep raw head (r w) (r x) := by
  simp only [hasStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (raw head : Bool) (ρ : Fin 1 → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel (matrix raw head) ρ x y = step raw head (ρ 0) x y := by
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

theorem intro_selected {m} {Γ : Context m} (raw head : Bool) (w x y a : Fin m)
    (hb : Derives Γ (body raw head w x y a)) : Derives Γ (selected raw head w x y) := by
  apply Derives.exI a
  simpa only [Formula.instantiate, body_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb

theorem intro_hasSelected {m} {Γ : Context m} (raw head : Bool) (w x y : Fin m)
    (hy : Derives Γ (selected raw head w x y)) : Derives Γ (hasSelected raw head w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem intro_value {m} {Γ : Context m} (raw head : Bool) (w x y : Fin m)
    (hy : Derives Γ (step raw head w x y)) : Derives Γ (hasStep raw head w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

end PPAC.Migration.Internal.PairingProjectionSyntax
