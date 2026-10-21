import PPAC.Migration.Internal.ObjectStructuralListRoundTrip

/-! 首次到达Nil或空集的真实tail递归检查；定义不出现Valid或宿主判定器。 -/
namespace PPAC.Migration.Internal.StructuralListCheckSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax

def terminal {m} (w b : Fin m) : Formula m := (empty b).disj (nilCode w b)

def occurs {m} (w n r : Fin m) : Formula m := .ex
  ((iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)).conj (terminal w.castSucc (Fin.last m)))

def eventually {m} (w n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (occurs w.castSucc n.castSucc (Fin.last m)))

def before {m} (w n r : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) r.castSucc).imp (occurs w.castSucc n.castSucc (Fin.last m)).neg)

def checkedAt {m} (w n r b : Fin m) : Formula m :=
  (((Formula.mem r w).conj (iteration false w n r b)).conj (terminal w b)).conj (before w n r)

def checkValue {m} (w n b : Fin m) : Formula m := .ex
  (checkedAt w.castSucc n.castSucc (Fin.last m) b.castSucc)

def hasCheck {m} (w n : Fin m) : Formula m := .ex (checkValue w.castSucc n.castSucc (Fin.last m))

def checkFiber {m} (w n : Fin m) : Formula m := .ex
  ((checkValue w.castSucc n.castSucc (Fin.last m)).conj (.all
    ((checkValue w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def accepts {m} (w n : Fin m) : Formula m := .ex
  ((checkValue w.castSucc n.castSucc (Fin.last m)).conj (nilCode w.castSucc (Fin.last m)))

def rejects {m} (w n : Fin m) : Formula m := .ex
  ((checkValue w.castSucc n.castSucc (Fin.last m)).conj (empty (Fin.last m)))

def matrix : Formula 2 := eventually 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (eventually w.castSucc (Fin.last m))))

def occursMatrix : Formula 3 := occurs 0 1 2

theorem terminal_rename {m k} (w b : Fin m) (s : Fin m → Fin k) : (terminal w b).rename s = terminal (s w) (s b) := by
  simp only [terminal, Formula.rename, empty_rename, nilCode_rename]

theorem occurs_rename {m k} (w n r : Fin m) (s : Fin m → Fin k) : (occurs w n r).rename s = occurs (s w) (s n) (s r) := by
  simp only [occurs, Formula.rename, iteration_rename, terminal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem eventually_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (eventually w n).rename s = eventually (s w) (s n) := by
  simp only [eventually, Formula.rename, occurs_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem before_rename {m k} (w n r : Fin m) (s : Fin m → Fin k) : (before w n r).rename s = before (s w) (s n) (s r) := by
  simp only [before, Formula.rename, Formula.neg, occurs_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem checkedAt_rename {m k} (w n r b : Fin m) (s : Fin m → Fin k) : (checkedAt w n r b).rename s = checkedAt (s w) (s n) (s r) (s b) := by
  simp only [checkedAt, Formula.rename, iteration_rename, terminal_rename, before_rename]

theorem checkValue_rename {m k} (w n b : Fin m) (s : Fin m → Fin k) : (checkValue w n b).rename s = checkValue (s w) (s n) (s b) := by
  simp only [checkValue, Formula.rename, checkedAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasCheck_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (hasCheck w n).rename s = hasCheck (s w) (s n) := by
  simp only [hasCheck, Formula.rename, checkValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem checkFiber_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (checkFiber w n).rename s = checkFiber (s w) (s n) := by
  simp only [checkFiber, Formula.rename, checkValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem accepts_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (accepts w n).rename s = accepts (s w) (s n) := by
  simp only [accepts, Formula.rename, checkValue_rename, nilCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rejects_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (rejects w n).rename s = rejects (s w) (s n) := by
  simp only [rejects, Formula.rename, checkValue_rename, empty_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (earlier w n).rename s = earlier (s w) (s n) := by
  simp only [earlier, Formula.rename, eventually_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = eventually (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, eventually_rename, h0, h1]

theorem occursMatrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred occursMatrix ρ x = occurs (ρ 0) (ρ 1) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, occursMatrix, occurs_rename, h0, h1, h2]

def params2 {m} (w n : Fin m) : Fin 2 → Fin m := Fin.lastCases n (fun _ => w)

theorem params2_0 {m} (w n : Fin m) : params2 w n 0 = w := by
  change Fin.lastCases n (fun _ : Fin 1 => w) (0 : Fin 1).castSucc = w
  exact Fin.lastCases_castSucc _

theorem params2_1 {m} (w n : Fin m) : params2 w n 1 = n := Fin.lastCases_last

theorem intro_occurs {m} {Γ : Context m} (w n r b : Fin m) (hb : Derives Γ (iteration false w n r b))
    (ht : Derives Γ (terminal w b)) : Derives Γ (occurs w n r) := by
  apply Derives.exI b
  simpa only [Formula.instantiate, Formula.rename, iteration_rename, terminal_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hb ht

theorem intro_eventually {m} {Γ : Context m} (w n r b : Fin m) (hr : Derives Γ (.mem r w))
    (hb : Derives Γ (iteration false w n r b)) (ht : Derives Γ (terminal w b)) : Derives Γ (eventually w n) := by
  apply Derives.exI r
  simp only [Formula.instantiate, Formula.rename, occurs_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hr (intro_occurs w n r b hb ht)

theorem before_at {m} {Γ : Context m} (w n r i : Fin m) (hb : Derives Γ (before w n r)) (hi : Derives Γ (.mem i r)) :
    Derives Γ (occurs w n i).neg := by
  have h : Derives Γ ((Formula.mem i r).imp (occurs w n i).neg) := by
    simpa only [before, Formula.instantiate, Formula.rename, Formula.neg, occurs_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i hb
  exact .impE h hi

theorem earlier_at {m} {Γ : Context m} (w n t : Fin m) (hi : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (hn : Derives Γ (.mem t n)) : Derives Γ (eventually w t) := by
  have h : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (eventually w t))) := by
    simpa only [earlier, Formula.instantiate, Formula.rename, eventually_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE t hi
  exact .impE (.impE h ht) hn

theorem intro_check {m} {Γ : Context m} (w n r b : Fin m) (ha : Derives Γ (checkedAt w n r b)) : Derives Γ (checkValue w n b) := by
  apply Derives.exI r
  simpa only [Formula.instantiate, checkedAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ha
theorem intro_hasCheck {m} {Γ : Context m} (w n b : Fin m) (hb : Derives Γ (checkValue w n b)) : Derives Γ (hasCheck w n) := by
  apply Derives.exI b
  simpa only [Formula.instantiate, checkValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb
end PPAC.Migration.Internal.StructuralListCheckSyntax
