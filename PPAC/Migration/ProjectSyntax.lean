import PPAC.Migration.SyntaxTransport
import YesMetaZFC.SetTheory.Definitional.Project.Derivation
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Syntax

/-! 源末变量语法到原Project首变量语法；所有参数保留，闭合证书由内核证明。 -/
namespace PPAC.Migration.ProjectSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
namespace P
export SetTheory.Definitional.Project (Formula Term Sentence UnarySchema BinarySchema fo_formula fo_bound_variable)
end P
attribute [local implicit_reducible] SetTheory.signature

def lift {n m} (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.lastCases 0 (fun i => (ρ i).succ)

def encode {n m} (ρ : Fin n → Fin m) : Source.Formula n → P.Formula 1 m
  | .bot => .falsum
  | .mem x y => .mem (.bound (ρ x)) (.bound (ρ y))
  | .equal x y => SetTheory.Definitional.Project.Formula.extensionalEq (.bound (ρ x)) (.bound (ρ y))
  | .imp p q => .imp (encode ρ p) (encode ρ q)
  | .conj p q => .conj (encode ρ p) (encode ρ q)
  | .disj p q => .disj (encode ρ p) (encode ρ q)
  | .all p => .forallE (encode (lift ρ) p)
  | .ex p => .existsE (encode (lift ρ) p)

theorem freeClosed {n m} (ρ : Fin n → Fin m) (p : Source.Formula n) :
    (encode ρ p).FreeClosed := by
  induction p generalizing m with
  | bot | mem => simp [encode, SetTheory.Definitional.Formula.FreeClosed]
  | equal => simp [encode]
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simpa only [encode, SetTheory.Definitional.Formula.FreeClosed] using And.intro (ihp ρ) (ihq ρ)
  | all p ih | ex p ih =>
      simpa only [encode, SetTheory.Definitional.Formula.FreeClosed] using ih (lift ρ)

theorem lift_comp {n m k} (ρ : Fin m → Fin k) (r : Fin n → Fin m) :
    (fun i => lift ρ (Source.Formula.liftRen r i)) = lift (fun i => ρ (r i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [lift, Source.Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rename_source {n m k} (ρ : Fin m → Fin k) (r : Fin n → Fin m) (p : Source.Formula n) :
    encode ρ (p.rename r) = encode (fun i => ρ (r i)) p := by
  induction p generalizing m k with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [Source.Formula.rename, encode, ihp, ihq]
  | all p ih | ex p ih => simp only [Source.Formula.rename, encode, ih, lift_comp]

theorem bound_lift {n m} (ρ : Fin n → Fin m) :
    (fun i => P.fo_bound_variable (lift ρ i)) =
      Translation.lift (fun i => P.fo_bound_variable (ρ i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [lift, Translation.lift, Fin.lastCases_last, Fin.lastCases_castSucc,
      P.fo_bound_variable, Fin.cases_zero, Fin.cases_succ]

/-- 两条独立的原生语言入口得到同一公式，而非仅仅在模型中真值相同。 -/
theorem fo_encode {n m} (ρ : Fin n → Fin m) (p : Source.Formula n) :
    P.fo_formula (encode ρ p) (freeClosed ρ p) =
      Translation.formula (fun i => P.fo_bound_variable (ρ i)) p := by
  induction p generalizing m with
  | bot | mem | equal =>
      simp only [encode, P.fo_formula, Translation.formula,
        SetTheory.Definitional.Project.fo_mem, SetTheory.Definitional.Project.fo_term,
        SetTheory.Definitional.Project.Formula.extensionalEq,
        SetTheory.Definitional.Project.Formula.pairArguments_get_zero,
        SetTheory.Definitional.Project.Formula.pairArguments_get_one]
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [encode, P.fo_formula, Translation.formula, ihp, ihq]
  | all p ih | ex p ih =>
      simp only [encode, P.fo_formula, Translation.formula, ih, bound_lift]

theorem lift_reverse {n} : lift (Fin.rev : Fin n → Fin n) = Fin.rev := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [lift, Fin.lastCases_last, Fin.lastCases_castSucc, Fin.rev_last, Fin.rev_castSucc]

def formula {n} (p : Source.Formula n) : P.Formula 1 n := encode Fin.rev p

theorem all_formula {n} (p : Source.Formula (n+1)) :
    formula (.all p) = .forallE (formula p) := by
  simp only [formula, encode, lift_reverse]

theorem close_formula {n} (p : Source.Formula n) :
    formula p.close = SetTheory.Definitional.Project.Formula.forallClosure n (formula p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Source.Formula.close, ih, all_formula]
      rfl

def unary {n} (p : Source.Formula (n+1)) : P.UnarySchema n :=
  ⟨formula p, freeClosed Fin.rev p⟩

def binary {n} (p : Source.Formula (n+2)) : P.BinarySchema n :=
  ⟨formula p, freeClosed Fin.rev p⟩
def headLift {m k} (r : Fin m → Fin k) : Fin (m+1) → Fin (k+1) :=
  Fin.cases 0 (fun i => (r i).succ)

theorem lift_bound_terms {m k} (r : Fin m → Fin k) :
    SetTheory.Definitional.Term.liftSubstitution (fun i => .bound (r i)) =
      (fun i => .bound (headLift r i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem rename_forall {m k} (r : Fin m → Fin k) (p : P.Formula 1 (m+1)) :
    SetTheory.Definitional.Formula.rename r (.forallE p) =
      .forallE (p.rename (headLift r)) := by
  simp only [SetTheory.Definitional.Formula.rename, SetTheory.Definitional.Formula.bind,
    Function.comp_def, lift_bound_terms]

theorem rename_exists {m k} (r : Fin m → Fin k) (p : P.Formula 1 (m+1)) :
    SetTheory.Definitional.Formula.rename r (.existsE p) =
      .existsE (p.rename (headLift r)) := by
  simp only [SetTheory.Definitional.Formula.rename, SetTheory.Definitional.Formula.bind,
    Function.comp_def, lift_bound_terms]

theorem head_lift_comp {n m k} (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (fun i => headLift r (lift ρ i)) = lift (fun i => r (ρ i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [headLift, lift, Fin.lastCases_last, Fin.lastCases_castSucc,
      Fin.cases_zero, Fin.cases_succ]

theorem rename_project {n m k} (ρ : Fin n → Fin m) (r : Fin m → Fin k) (p : Source.Formula n) :
    (encode ρ p).rename r = encode (fun i => r (ρ i)) p := by
  induction p generalizing m k with
  | bot | mem | equal =>
      simp [encode, SetTheory.Definitional.Formula.rename, SetTheory.Definitional.Formula.bind,
        SetTheory.Definitional.Project.Formula.extensionalEq,
        SetTheory.Definitional.Project.Formula.pairArguments,
        SetTheory.Definitional.TermVector.bind, SetTheory.Definitional.Term.bind]
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [encode, SetTheory.Definitional.Formula.rename,
        SetTheory.Definitional.Formula.bind] at *
      rw [ihp, ihq]
  | all p ih =>
      simp only [encode, rename_forall, ih, head_lift_comp]
  | ex p ih =>
      simp only [encode, rename_exists, ih, head_lift_comp]
theorem fo_congr {depth} {p q : P.Formula 1 depth}
    {hp : p.FreeClosed} {hq : q.FreeClosed} (h : p = q) :
    P.fo_formula p hp = P.fo_formula q hq := by
  cases h
  rfl
end PPAC.Migration.ProjectSyntax
