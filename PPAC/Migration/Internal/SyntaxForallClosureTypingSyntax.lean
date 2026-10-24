import PPAC.Migration.Internal.SyntaxUnaryIterationLaws

/-! Object-uniform typing property: remaining scope and output vary inside ALL2. -/
namespace PPAC.Migration.Internal.SyntaxForallClosureTypingSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalUniversalBlock
open SyntaxRenameQuerySyntax (of_eq)

def correctAt {m} (w a source f n b y : Fin m) : Formula m :=
  (Formula.mem b w).imp ((NaturalAdditionSyntax.sum w n b source).imp
    ((SyntaxUnaryIterationSyntax.forallClosure w a n y).imp
      ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f))))

def body {m} (w a source f n : Fin m) : Formula (m+2) :=
  correctAt (old 2 w) (old 2 a) (old 2 source) (old 2 f) (old 2 n) (slot 2 0) (slot 2 1)

def correct {m} (w a source f n : Fin m) : Formula m := allMany 2 (body w a source f n)

theorem correctAt_rename {m l} (w a source f n b y : Fin m) (ρ : Fin m → Fin l) :
    (correctAt w a source f n b y).rename ρ = correctAt (ρ w) (ρ a) (ρ source) (ρ f) (ρ n) (ρ b) (ρ y) := by
  simp only [correctAt, Formula.rename, Formula.iff, NaturalAdditionSyntax.sum_rename,
    SyntaxUnaryIterationSyntax.forallClosure_rename, FormulaCodeSyntax.formulaCode_rename]

theorem body_lift {m l} (w a source f n : Fin m) (ρ : Fin m → Fin l) :
    (body w a source f n).rename (lift 2 ρ) = body (ρ w) (ρ a) (ρ source) (ρ f) (ρ n) := by
  simp only [body, correctAt_rename, lift_old, lift_slot]

theorem correct_rename {m l} (w a source f n : Fin m) (ρ : Fin m → Fin l) :
    (correct w a source f n).rename ρ = correct (ρ w) (ρ a) (ρ source) (ρ f) (ρ n) := by
  simp only [correct, allMany_rename, body_lift]

theorem at_point {m} {Γ : Context m} (w a source f n b y : Fin m)
    (hi : Derives Γ (correct w a source f n)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w n b source))
    (hy : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f)) := by
  have h := at_many 2 (body w a source f n) (Source.SetLanguage.args2 b y) hi
  have h' : Derives Γ (correctAt w a source f n b y) := of_eq (by
    simp only [body, correctAt_rename, assign_old, assign_slot]; rfl) h
  exact .impE (.impE (.impE h' hb) hs) hy

def matrix : Formula 5 := correct (0 : Fin 5) 1 2 3 4

def parameters {m} (w a source f : Fin m) : Fin 4 → Fin m :=
  Fin.cases w (Fin.cases a (Fin.cases source (fun _ => f)))

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = correct (ρ 0) (ρ 1) (ρ 2) (ρ 3) n := by
  simp only [MinimalPredicates.pred, matrix, correct_rename]
  rfl

end PPAC.Migration.Internal.SyntaxForallClosureTypingSyntax
