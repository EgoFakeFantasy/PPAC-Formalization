import PPAC.Migration.Internal.ObjectLookupTableProgram
import YesMetaZFC.Automation.ObjectSyntaxTransform

/-! 直接编译上游 ObjectHorn.Expr。表达式仅为外部固定模式；所有运行值均为内部对象。 -/
namespace PPAC.Migration.Internal.HornExprSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def environmentNat {m} : (n : Nat) → Fin m → (Fin n → Fin m) → Formula m
  | 0, _, _ => (.imp .bot .bot)
  | n+1, w, env => (Formula.mem (env 0) w).conj (environmentNat n w (fun i => env i.succ))

def graph {m n} : Expr n → Fin m → (Fin n → Fin m) → Fin m → Formula m
  | .literal k, _, _, y => SyntaxNumeralSyntax.numeral k y
  | .var i, w, env, y => (Formula.mem (env i) w).conj (.equal y (env i))
  | .succ e, w, env, y => .ex
      ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (successor y.castSucc (Fin.last m)))
  | .pair e f, w, env, y => .ex (.ex
      ((graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj
        ((graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj
          (GodelPairSyntax.code w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))))

def existsValue {m n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)))

def uniqueValue {m n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) (y : Fin m) : Formula m := .all
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def fiber {m n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) : Formula m := .ex
  ((graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj
    ((Formula.mem (Fin.last m) w.castSucc).conj (uniqueValue e w.castSucc (fun i => (env i).castSucc) (Fin.last m))))

theorem environmentNat_rename {m k} (n : Nat) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (environmentNat n w env).rename ρ = environmentNat n (ρ w) (fun i => ρ (env i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [environmentNat, Formula.rename, ih]

theorem environmentNat_at {m n} {Γ : Context m} (w : Fin m) (env : Fin n → Fin m)
    (he : Derives Γ (environmentNat n w env)) (i : Fin n) : Derives Γ (.mem (env i) w) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact .conjL he
    | succ i => exact ih (fun j => env j.succ) (.conjR he) i

theorem graph_rename {m k n} (e : Expr n) (w y : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (graph e w env y).rename ρ = graph e (ρ w) (fun i => ρ (env i)) (ρ y) := by
  induction e generalizing m k with
  | literal value => exact SyntaxNumeralSyntax.numeral_rename value y ρ
  | var index => rfl
  | succ e ih => simp only [graph, Formula.rename, ih, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
  | pair e f ih ihf => simp only [graph, Formula.rename, ih, ihf, GodelPairSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsValue_rename {m k n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (existsValue e w env).rename ρ = existsValue e (ρ w) (fun i => ρ (env i)) := by
  simp only [existsValue, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueValue_rename {m k n} (e : Expr n) (w y : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (uniqueValue e w env y).rename ρ = uniqueValue e (ρ w) (fun i => ρ (env i)) (ρ y) := by
  simp only [uniqueValue, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k n} (e : Expr n) (w : Fin m) (env : Fin n → Fin m) (ρ : Fin m → Fin k) :
    (fiber e w env).rename ρ = fiber e (ρ w) (fun i => ρ (env i)) := by
  simp only [fiber, Formula.rename, graph_rename, uniqueValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_existsValue {m n} {Γ : Context m} (e : Expr n) (w y : Fin m) (env : Fin n → Fin m)
    (hy : Derives Γ (.mem y w)) (hg : Derives Γ (graph e w env y)) : Derives Γ (existsValue e w env) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hy hg)

theorem intro_succ {m n} {Γ : Context m} (e : Expr n) (w y x : Fin m) (env : Fin n → Fin m)
    (hx : Derives Γ (graph e w env x)) (hy : Derives Γ (successor y x)) : Derives Γ (graph (.succ e) w env y) := by
  apply Derives.exI x
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hx hy)

theorem intro_pair {m n} {Γ : Context m} (e f : Expr n) (w y a b : Fin m) (env : Fin n → Fin m)
    (ha : Derives Γ (graph e w env a)) (hb : Derives Γ (graph f w env b))
    (hy : Derives Γ (GodelPairSyntax.code w a b y)) : Derives Γ (graph (.pair e f) w env y) := by
  apply Derives.exI a
  apply Derives.exI b
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, GodelPairSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI ha (.conjI hb hy))

theorem output_subst {m n} {Γ : Context m} (e : Expr n) (w x y : Fin m) (env : Fin n → Fin m)
    (he : Derives Γ (.equal x y)) (hx : Derives Γ (graph e w env x)) : Derives Γ (graph e w env y) := by
  let P := graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)
  have h0 : P.instantiate x = graph e w env x := by simp only [P, Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate y = graph e w env y := by simp only [P, Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

end PPAC.Migration.Internal.HornExprSyntax
