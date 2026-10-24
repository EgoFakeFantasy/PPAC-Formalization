import PPAC.Migration.Internal.ObjectProjectAtomic

/-! Independent source grammar for the three Project atoms and two constants. -/
namespace PPAC.Migration.Internal.ProjectSourceAtomSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def binaryBody {m} (kind : Fin 3) (w b n : Fin m) : Formula (m+2) :=
  ProjectAtomicSyntax.sourceAt kind (old 2 w) (old 2 b) (slot 2 0) (slot 2 1) (old 2 n)

def binaryAtom {m} (kind : Fin 3) (w b n : Fin m) : Formula m := existsMany 2 (binaryBody kind w b n)

def atomic {m} (w b f n : Fin m) : Formula m :=
  ((SyntaxAtomSyntax.nullary false w b f n).disj (SyntaxAtomSyntax.nullary true w b f n)).disj
    ((SyntaxTermSyntax.contexts w b f).conj ((binaryAtom 0 w b n).disj ((binaryAtom 1 w b n).disj (binaryAtom 2 w b n))))

theorem binaryBody_lift {m l} (kind : Fin 3) (w b n : Fin m) (ρ : Fin m → Fin l) :
    (binaryBody kind w b n).rename (lift 2 ρ) = binaryBody kind (ρ w) (ρ b) (ρ n) := by
  simp only [binaryBody, ProjectAtomicSyntax.sourceAt_rename, lift_old, lift_slot]

theorem binaryAtom_rename {m l} (kind : Fin 3) (w b n : Fin m) (ρ : Fin m → Fin l) :
    (binaryAtom kind w b n).rename ρ = binaryAtom kind (ρ w) (ρ b) (ρ n) := by
  simp only [binaryAtom, existsMany_rename, binaryBody_lift]

theorem atomic_rename {m l} (w b f n : Fin m) (ρ : Fin m → Fin l) :
    (atomic w b f n).rename ρ = atomic (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [atomic, Formula.rename, SyntaxAtomSyntax.nullary_rename, SyntaxTermSyntax.contexts_rename, binaryAtom_rename]

theorem intro_binary {m} {Γ : Context m} (kind : Fin 3) (w b x y n : Fin m)
    (hi : Derives Γ (ProjectAtomicSyntax.sourceAt kind w b x y n)) : Derives Γ (binaryAtom kind w b n) := by
  apply HornBinderRules.intro_many 2 (binaryBody kind w b n) (SyntaxAtomSyntax.two x y)
  exact of_eq (by simp only [binaryBody, ProjectAtomicSyntax.sourceAt_rename, assign_old, assign_slot]; rfl) hi

end PPAC.Migration.Internal.ProjectSourceAtomSyntax
