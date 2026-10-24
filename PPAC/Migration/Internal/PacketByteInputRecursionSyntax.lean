import PPAC.Migration.Internal.PacketByteInputProperties

/-! Exact byte input criteria retain real Cons and independent smaller input guards. -/
namespace PPAC.Migration.Internal.PacketByteInputRecursionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def consBody {m} (w C n : Fin m) : Formula (m+2) :=
  (StructuralListSyntax.consCode (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)).conj
    ((Formula.mem (slot 2 0) (old 2 C)).conj (inputAt (old 2 w) (old 2 C) (slot 2 1)))

def consCase {m} (w C n : Fin m) : Formula m := existsMany 2 (consBody w C n)

def criterionAt {m} (w C n : Fin m) : Formula m := (StructuralListSyntax.nilCode w n).disj (consCase w C n)

def actualBody {m} (w n : Fin m) : Formula (m+2) :=
  (StructuralListSyntax.consCode (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)).conj
    ((byte (slot 2 0)).conj (byteList (old 2 w) (slot 2 1)))

def actualCons {m} (w n : Fin m) : Formula m := existsMany 2 (actualBody w n)

def criterion {m} (w n : Fin m) : Formula m := (StructuralListSyntax.nilCode w n).disj (actualCons w n)

theorem consBody_lift {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (consBody w C n).rename (lift 2 ρ) = consBody (ρ w) (ρ C) (ρ n) := by
  simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,inputAt_rename,lift_old,lift_slot]

theorem consCase_rename {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (consCase w C n).rename ρ = consCase (ρ w) (ρ C) (ρ n) := by
  simp only [consCase,existsMany_rename,consBody_lift]

theorem criterionAt_rename {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (criterionAt w C n).rename ρ = criterionAt (ρ w) (ρ C) (ρ n) := by
  simp only [criterionAt,Formula.rename,StructuralListSyntax.nilCode_rename,consCase_rename]

theorem actualBody_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (actualBody w n).rename (lift 2 ρ) = actualBody (ρ w) (ρ n) := by
  simp only [actualBody,Formula.rename,StructuralListSyntax.consCode_rename,byte_rename,byteList_rename,lift_old,lift_slot]

theorem actualCons_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (actualCons w n).rename ρ = actualCons (ρ w) (ρ n) := by
  simp only [actualCons,existsMany_rename,actualBody_lift]

theorem criterion_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (criterion w n).rename ρ = criterion (ρ w) (ρ n) := by
  simp only [criterion,Formula.rename,StructuralListSyntax.nilCode_rename,actualCons_rename]

theorem intro_cons {m} {Γ : Context m} (w C n h t : Fin m) (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hh : Derives Γ (.mem h C)) (ht : Derives Γ (inputAt w C t)) : Derives Γ (consCase w C n) := by
  apply HornBinderRules.intro_many 2 (consBody w C n) (SyntaxAtomSyntax.two h t)
  exact of_eq (by simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,inputAt_rename,assign_old,assign_slot]; rfl) (.conjI hc (.conjI hh ht))

theorem intro_actual_cons {m} {Γ : Context m} (w n h t : Fin m) (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hh : Derives Γ (byte h)) (ht : Derives Γ (byteList w t)) : Derives Γ (actualCons w n) := by
  apply HornBinderRules.intro_many 2 (actualBody w n) (SyntaxAtomSyntax.two h t)
  exact of_eq (by simp only [actualBody,Formula.rename,StructuralListSyntax.consCode_rename,byte_rename,byteList_rename,assign_old,assign_slot]; rfl) (.conjI hc (.conjI hh ht))

end PPAC.Migration.Internal.PacketByteInputRecursionSyntax
