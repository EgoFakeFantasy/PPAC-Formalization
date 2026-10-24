import PPAC.Migration.Internal.ProjectCompilerUniqueTransport
import PPAC.Migration.Internal.ProofTreeRootSyntax

/-! Twelve external finite templates for the actual program; all fields and codes remain object variables. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueMatrixSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerCaseSyntax ProjectCompilerRecursiveSyntax

inductive Mode where
  | falseCase
  | trueCase
  | memberCase
  | equalCase
  | subsetCase
  | negCase
  | conjCase
  | disjCase
  | impCase
  | iffCase
  | forallCase
  | existsCase
  deriving DecidableEq

def modes : List Mode := [.falseCase, .trueCase, .memberCase, .equalCase, .subsetCase, .negCase, .conjCase, .disjCase, .impCase, .iffCase, .forallCase, .existsCase]

theorem mode_mem (mode : Mode) : mode ∈ modes := by
  cases mode <;> decide

def tag : Mode → Nat
  | .falseCase => 0
  | .trueCase => 1
  | .memberCase => 2
  | .equalCase => 3
  | .subsetCase => 11
  | .negCase => 4
  | .conjCase => 5
  | .disjCase => 6
  | .impCase => 7
  | .iffCase => 8
  | .forallCase => 9
  | .existsCase => 10

def arity : Mode → Nat
  | .falseCase => 0
  | .trueCase => 0
  | .memberCase => 2
  | .equalCase => 2
  | .subsetCase => 2
  | .negCase => 1
  | .conjCase => 2
  | .disjCase => 2
  | .impCase => 2
  | .iffCase => 2
  | .forallCase => 1
  | .existsCase => 1

def inputs {m} (mode : Mode) (xs : Fin 4 → Fin m) : Fin (arity mode) → Fin m := by
  cases mode
  · exact Fin.elim0
  · exact Fin.elim0
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact (fun _ => xs 0)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact SyntaxAtomSyntax.two (xs 0) (xs 1)
  · exact (fun _ => xs 0)
  · exact (fun _ => xs 0)

theorem tag_injective {a b : Mode} (h : tag a = tag b) : a = b := by
  cases a <;> cases b <;> simp_all [tag]

def matrix {m} (mode : Mode) (w b z n q : Fin m) (xs : Fin 4 → Fin m) : Formula m :=
  match mode with
  | .falseCase => constant false w n q
  | .trueCase => constant true w n q
  | .memberCase => ProjectAtomicSyntax.compiled 0 w b z (xs 0) (xs 1) n q
  | .equalCase => ProjectAtomicSyntax.compiled 1 w b z (xs 0) (xs 1) n q
  | .subsetCase => ProjectAtomicSyntax.compiled 2 w b z (xs 0) (xs 1) n q
  | .negCase => singleMatrix 4 false codeMatrix (parameters w) w b n q (xs 0) (xs 1)
  | .conjCase => binaryMatrix 0 codeMatrix (parameters w) w b n q (xs 0) (xs 1) (xs 2) (xs 3)
  | .disjCase => binaryMatrix 1 codeMatrix (parameters w) w b n q (xs 0) (xs 1) (xs 2) (xs 3)
  | .impCase => binaryMatrix 2 codeMatrix (parameters w) w b n q (xs 0) (xs 1) (xs 2) (xs 3)
  | .iffCase => binaryMatrix 3 codeMatrix (parameters w) w b n q (xs 0) (xs 1) (xs 2) (xs 3)
  | .forallCase => singleMatrix 9 true codeMatrix (parameters w) w b n q (xs 0) (xs 1)
  | .existsCase => singleMatrix 10 true codeMatrix (parameters w) w b n q (xs 0) (xs 1)

theorem matrix_rename {m j} (mode : Mode) (w b z n q : Fin m) (xs : Fin 4 → Fin m) (σ : Fin m → Fin j) :
    (matrix mode w b z n q xs).rename σ = matrix mode (σ w) (σ b) (σ z) (σ n) (σ q) (fun i => σ (xs i)) := by
  cases mode <;> simp only [matrix, constant_rename, ProjectAtomicSyntax.compiled_rename,
    singleMatrix_rename, binaryMatrix_rename, parameters_map]

def body {m} (mode : Mode) (w b z n q : Fin m) : Formula (m+4) :=
  matrix mode (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 q) (slot 4)

def uniformCase {m} (mode : Mode) (w b z n q : Fin m) : Formula m := existsMany 4 (body mode w b z n q)

theorem body_lift {m j} (mode : Mode) (w b z n q : Fin m) (σ : Fin m → Fin j) :
    (body mode w b z n q).rename (lift 4 σ) = body mode (σ w) (σ b) (σ z) (σ n) (σ q) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem uniformCase_rename {m j} (mode : Mode) (w b z n q : Fin m) (σ : Fin m → Fin j) :
    (uniformCase mode w b z n q).rename σ = uniformCase mode (σ w) (σ b) (σ z) (σ n) (σ q) := by
  simp only [uniformCase, existsMany_rename, body_lift]

def choices {m} (w b z n q : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (modes.map (fun mode => uniformCase mode w b z n q))

theorem choices_rename {m j} (w b z n q : Fin m) (σ : Fin m → Fin j) :
    (choices w b z n q).rename σ = choices (σ w) (σ b) (σ z) (σ n) (σ q) := by
  unfold choices
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro mode _
  exact uniformCase_rename mode w b z n q σ

end PPAC.Migration.Internal.ProjectCompilerUniqueMatrixSyntax
