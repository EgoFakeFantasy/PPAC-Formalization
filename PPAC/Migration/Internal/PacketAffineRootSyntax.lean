import PPAC.Migration.Internal.PacketAffineRootTransport

/-! Exact predecessor equation at specified internal Packet root fields. -/
namespace PPAC.Migration.Internal.PacketAffineRootSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def zeroCase {m} (B d t n : Fin m) : Formula m := (empty t).conj ((Formula.mem d B).conj (.equal n d))

def predecessorBody {m} (wide : Bool) (w B V d t n : Fin m) : Formula (m+2) :=
  (successor (old 2 t) (slot 2 0)).conj
    ((NaturalAdditionSyntax.sum (old 2 w) (slot 2 1) (old 2 B) (old 2 n)).conj
      (PacketHornAffineSyntax.entry wide (old 2 w) (old 2 V) (old 2 d) (slot 2 0) (slot 2 1)))

def predecessor {m} (wide : Bool) (w B V d t n : Fin m) : Formula m := existsMany 2 (predecessorBody wide w B V d t n)

def criterion {m} (wide : Bool) (w B V d t n : Fin m) : Formula m := (zeroCase B d t n).disj (predecessor wide w B V d t n)

theorem zeroCase_rename {m j} (B d t n : Fin m) (ρ : Fin m → Fin j) :
    (zeroCase B d t n).rename ρ = zeroCase (ρ B) (ρ d) (ρ t) (ρ n) := by
  simp only [zeroCase, Formula.rename, empty_rename]

theorem predecessorBody_lift {m j} (wide : Bool) (w B V d t n : Fin m) (ρ : Fin m → Fin j) :
    (predecessorBody wide w B V d t n).rename (lift 2 ρ) = predecessorBody wide (ρ w) (ρ B) (ρ V) (ρ d) (ρ t) (ρ n) := by
  simp only [predecessorBody, Formula.rename, successor_rename, NaturalAdditionSyntax.sum_rename,
    PacketHornAffineSyntax.entry_rename, lift_old, lift_slot]

theorem predecessor_rename {m j} (wide : Bool) (w B V d t n : Fin m) (ρ : Fin m → Fin j) :
    (predecessor wide w B V d t n).rename ρ = predecessor wide (ρ w) (ρ B) (ρ V) (ρ d) (ρ t) (ρ n) := by
  simp only [predecessor, existsMany_rename, predecessorBody_lift]

theorem criterion_rename {m j} (wide : Bool) (w B V d t n : Fin m) (ρ : Fin m → Fin j) :
    (criterion wide w B V d t n).rename ρ = criterion wide (ρ w) (ρ B) (ρ V) (ρ d) (ρ t) (ρ n) := by
  simp only [criterion, Formula.rename, zeroCase_rename, predecessor_rename]

theorem intro_predecessor {m} {Γ : Context m} (wide : Bool) (w B V d t n p a : Fin m)
    (hs : Derives Γ (successor t p)) (hn : Derives Γ (NaturalAdditionSyntax.sum w a B n))
    (he : Derives Γ (PacketHornAffineSyntax.entry wide w V d p a)) : Derives Γ (predecessor wide w B V d t n) := by
  apply HornBinderRules.intro_many 2 (predecessorBody wide w B V d t n) (SyntaxAtomSyntax.two p a)
  exact of_eq (by simp only [predecessorBody, Formula.rename, successor_rename, NaturalAdditionSyntax.sum_rename,
    PacketHornAffineSyntax.entry_rename, assign_old, assign_slot]; rfl) (.conjI hs (.conjI hn he))

end PPAC.Migration.Internal.PacketAffineRootSyntax
