import PPAC.Migration.Internal.PacketTokenRootTransport

/-! Specified token fields keep exactly the remaining original five large witnesses. -/
namespace PPAC.Migration.Internal.PacketTokenRootSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)

def five {m} (d q u z y : Fin m) : Fin 5 → Fin m :=
  Fin.cases d (Fin.cases q (Fin.cases u (Fin.cases z (Fin.cases y Fin.elim0))))

def smallCase {m} (w B V n t a : Fin m) : Formula m := (Formula.mem n B).conj (tagEntry 1 w V n t a)

def largeBody {m} (w B V n t a : Fin m) : Formula (m+5) :=
  (empty (slot 5 3)).conj ((NaturalAdditionSyntax.sum (old 5 w) (slot 5 0) (old 5 B) (slot 5 4)).conj
    (((Formula.mem (slot 5 3) (slot 5 1)).conj (.mem (slot 5 0) (old 5 B))).conj
      ((tagEntry 0 (old 5 w) (old 5 V) (slot 5 0) (slot 5 1) (old 5 n)).conj
        ((entry (old 5 w) (old 5 V) (slot 5 1) (old 5 t) (slot 5 2)).conj
          (tagEntry 1 (old 5 w) (old 5 V) (slot 5 4) (slot 5 2) (old 5 a))))))

def largeCase {m} (w B V n t a : Fin m) : Formula m := existsMany 5 (largeBody w B V n t a)

def criterion {m} (w B V n t a : Fin m) : Formula m := (smallCase w B V n t a).disj (largeCase w B V n t a)

theorem smallCase_rename {m j} (w B V n t a : Fin m) (ρ : Fin m → Fin j) :
    (smallCase w B V n t a).rename ρ = smallCase (ρ w) (ρ B) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [smallCase, Formula.rename, tagEntry_rename]

theorem largeBody_lift {m j} (w B V n t a : Fin m) (ρ : Fin m → Fin j) :
    (largeBody w B V n t a).rename (lift 5 ρ) = largeBody (ρ w) (ρ B) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [largeBody, Formula.rename, empty_rename, NaturalAdditionSyntax.sum_rename, tagEntry_rename, entry_rename, lift_old, lift_slot]

theorem largeCase_rename {m j} (w B V n t a : Fin m) (ρ : Fin m → Fin j) :
    (largeCase w B V n t a).rename ρ = largeCase (ρ w) (ρ B) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [largeCase, existsMany_rename, largeBody_lift]

theorem criterion_rename {m j} (w B V n t a : Fin m) (ρ : Fin m → Fin j) :
    (criterion w B V n t a).rename ρ = criterion (ρ w) (ρ B) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [criterion, Formula.rename, smallCase_rename, largeCase_rename]

theorem intro_large {m} {Γ : Context m} (w B V n t a d q u z y : Fin m)
    (hz : Derives Γ (empty z)) (hy : Derives Γ (NaturalAdditionSyntax.sum w d B y))
    (hg : Derives Γ ((Formula.mem z q).conj (.mem d B)))
    (hp : Derives Γ ((tagEntry 0 w V d q n).conj ((entry w V q t u).conj (tagEntry 1 w V y u a)))) :
    Derives Γ (largeCase w B V n t a) := by
  apply HornBinderRules.intro_many 5 (largeBody w B V n t a) (five d q u z y)
  exact of_eq (by simp only [largeBody, Formula.rename, empty_rename, NaturalAdditionSyntax.sum_rename,
    tagEntry_rename, entry_rename, assign_old, assign_slot]; rfl) (.conjI hz (.conjI hy (.conjI hg hp)))

end PPAC.Migration.Internal.PacketTokenRootSyntax
