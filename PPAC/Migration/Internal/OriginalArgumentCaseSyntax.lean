import PPAC.Migration.Internal.OriginalArgumentsMetadata

/-! 原参数列表两分支的纯数值对象公式；cons的四个实际组件均内部存在量化。 -/
namespace PPAC.Migration.Internal.OriginalArgumentCaseSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def nilData {m} (w input output : Fin m) : Formula m := (StructuralListSyntax.nilCode w input).conj (StructuralListSyntax.nilCode w output)

def consData {m} (w mode depth parameter input output h t H T : Fin m) : Formula m :=
  ((StructuralListSyntax.consCode w h t input).conj (StructuralListSyntax.consCode w H T output)).conj
    ((OriginalTransformRowSyntax.run 1 w mode depth parameter h H).conj (OriginalTransformRowSyntax.run 2 w mode depth parameter t T))

def consBody {m} (w mode depth parameter input output : Fin m) : Formula (m+4) :=
  consData (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 input) (old 4 output) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def consCase {m} (w mode depth parameter input output : Fin m) : Formula m := existsMany 4 (consBody w mode depth parameter input output)

def outcomes {m} (w mode depth parameter input output : Fin m) : Formula m :=
  (nilData w input output).disj (consCase w mode depth parameter input output)

theorem nilData_rename {m k} (w input output : Fin m) (ρ : Fin m → Fin k) :
    (nilData w input output).rename ρ = nilData (ρ w) (ρ input) (ρ output) := by
  simp only [nilData, Formula.rename, StructuralListSyntax.nilCode_rename]

theorem consData_rename {m k} (w mode depth parameter input output h t H T : Fin m) (ρ : Fin m → Fin k) :
    (consData w mode depth parameter input output h t H T).rename ρ = consData (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) (ρ h) (ρ t) (ρ H) (ρ T) := by
  simp only [consData, Formula.rename, StructuralListSyntax.consCode_rename, OriginalTransformRowSyntax.run_rename]

theorem consBody_lift {m k} (w mode depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (consBody w mode depth parameter input output).rename (lift 4 ρ) = consBody (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [consBody, consData_rename, lift_old, lift_slot]

theorem consCase_rename {m k} (w mode depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (consCase w mode depth parameter input output).rename ρ = consCase (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [consCase, existsMany_rename, consBody_lift]

theorem outcomes_rename {m k} (w mode depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (outcomes w mode depth parameter input output).rename ρ = outcomes (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [outcomes, Formula.rename, nilData_rename, consCase_rename]

theorem intro_cons {m} {Γ : Context m} (w mode depth parameter input output h t H T : Fin m)
    (hd : Derives Γ (consData w mode depth parameter input output h t H T)) :
    Derives Γ (consCase w mode depth parameter input output) := by
  apply HornBinderRules.intro_many 4 (consBody w mode depth parameter input output) (four h t H T)
  exact of_eq (by simp only [consBody, consData_rename, assign_old, assign_slot]; rfl) hd

end PPAC.Migration.Internal.OriginalArgumentCaseSyntax
