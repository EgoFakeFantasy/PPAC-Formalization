import PPAC.Migration.Internal.PacketTokenCanonicalEntry

/-! The arithmetic recurrence retains a real recursive accepted token, not an answer-defined predicate. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def four {m} (d q u y : Fin m) : Fin 4 → Fin m := Fin.cases d (Fin.cases q (Fin.cases u (Fin.cases y Fin.elim0)))

def smallCase {m} (w B C n t a : Fin m) : Formula m := (Formula.mem n B).conj (affine w C n t a)

def largeBody {m} (w B C n t a : Fin m) : Formula (m+4) :=
  (affine (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n)).conj
    ((empty (slot 4 1)).neg.conj ((NaturalAdditionSyntax.sum (old 4 w) (slot 4 0) (old 4 B) (slot 4 3)).conj
      ((accepted (old 4 w) (slot 4 1) (old 4 t) (slot 4 2)).conj
        (affine (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a)))))

def largeCase {m} (w B C n t a : Fin m) : Formula m := existsMany 4 (largeBody w B C n t a)

def criterion {m} (w B C n t a : Fin m) : Formula m := (smallCase w B C n t a).disj (largeCase w B C n t a)

theorem smallCase_rename {m j} (w B C n t a : Fin m) (ρ : Fin m → Fin j) :
    (smallCase w B C n t a).rename ρ = smallCase (ρ w) (ρ B) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [smallCase, Formula.rename, affine_rename]

theorem largeBody_lift {m j} (w B C n t a : Fin m) (ρ : Fin m → Fin j) :
    (largeBody w B C n t a).rename (lift 4 ρ) = largeBody (ρ w) (ρ B) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [largeBody, Formula.rename, affine_rename, empty_rename, NaturalAdditionSyntax.sum_rename,
    accepted_rename, lift_old, lift_slot]

theorem largeCase_rename {m j} (w B C n t a : Fin m) (ρ : Fin m → Fin j) :
    (largeCase w B C n t a).rename ρ = largeCase (ρ w) (ρ B) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [largeCase, existsMany_rename, largeBody_lift]

theorem criterion_rename {m j} (w B C n t a : Fin m) (ρ : Fin m → Fin j) :
    (criterion w B C n t a).rename ρ = criterion (ρ w) (ρ B) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [criterion, Formula.rename, smallCase_rename, largeCase_rename]

theorem intro_large {m} {Γ : Context m} (w B C n t a d q u y : Fin m)
    (h0 : Derives Γ (affine w B d q n)) (hq : Derives Γ (empty q).neg)
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B y)) (ht : Derives Γ (accepted w q t u))
    (h1 : Derives Γ (affine w C y u a)) : Derives Γ (largeCase w B C n t a) := by
  apply HornBinderRules.intro_many 4 (largeBody w B C n t a) (four d q u y)
  exact of_eq (by simp only [largeBody, Formula.rename, affine_rename, empty_rename,
    NaturalAdditionSyntax.sum_rename, accepted_rename, assign_old, assign_slot]; rfl)
    (.conjI h0 (.conjI hq (.conjI hs (.conjI ht h1))))

end PPAC.Migration.Internal.PacketTokenArithmeticSyntax
