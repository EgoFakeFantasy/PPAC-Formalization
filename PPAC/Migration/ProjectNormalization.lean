import PPAC.Migration.ProjectSyntax
import PPAC.Migration.Normalization

/-! 原Project连接词展开与纯语言原核规范化严格交换。 -/
namespace PPAC.Migration.ProjectNormalization
open YesMetaZFC YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
namespace P
export SetTheory.Definitional.Project (Formula fo_formula)
end P

def formula {depth} : P.Formula 1 depth → P.Formula 1 depth
  | .falsum => .falsum
  | .truth => .imp .falsum .falsum
  | .mem x y => .mem x y
  | .atom s h args => .atom s h args
  | .neg p => .imp (formula p) .falsum
  | .conj p q => .conj (formula p) (formula q)
  | .disj p q => .disj (formula p) (formula q)
  | .imp p q => .imp (formula p) (formula q)
  | .iff p q => .conj (.imp (formula p) (formula q)) (.imp (formula q) (formula p))
  | .forallE p => .forallE (formula p)
  | .existsE p => .existsE (formula p)

theorem freeClosed {depth} (p : P.Formula 1 depth) (h : p.FreeClosed) :
    (formula p).FreeClosed := by
  induction p <;> simp_all [formula, Definitional.Formula.FreeClosed]

theorem fo_formula {depth} (p : P.Formula 1 depth) (h : p.FreeClosed) :
    P.fo_formula (formula p) (freeClosed p h) = Normalization.formula (P.fo_formula p h) := by
  induction p with
  | falsum | truth | mem => simp only [formula, P.fo_formula, Normalization.formula,
      Definitional.Project.fo_mem]
  | atom s hs args =>
      cases s <;> simp only [formula, P.fo_formula, Normalization.formula, Definitional.Project.fo_mem]
  | neg p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, P.fo_formula, Normalization.formula, ih h]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, P.fo_formula, Normalization.formula, ihp h.1, ihq h.2]
  | forallE p ih | existsE p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, P.fo_formula, Normalization.formula, ih h]

theorem encode_fixed {n m} (ρ : Fin n → Fin m) (p : Source.Formula n) :
    formula (ProjectSyntax.encode ρ p) = ProjectSyntax.encode ρ p := by
  induction p generalizing m with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [ProjectSyntax.encode, formula, ihp, ihq]
  | all p ih | ex p ih => simp only [ProjectSyntax.encode, formula, ih]

theorem close_formula {depth} (p : P.Formula 1 depth) :
    formula (Definitional.Project.Formula.forallClosure depth p) =
      Definitional.Project.Formula.forallClosure depth (formula p) := by
  induction depth with
  | zero => rfl
  | succ n ih =>
      change formula (Definitional.Formula.forallClosure n (.forallE p)) = _
      rw [ih]
      rfl
end PPAC.Migration.ProjectNormalization
