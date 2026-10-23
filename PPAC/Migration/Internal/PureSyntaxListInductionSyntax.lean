import PPAC.Migration.Internal.PureSyntaxConsRule
import PPAC.Migration.Internal.OriginalUniversalBlock

/-! 全部内部参数量化的列表查询正确性及严格成员归纳前提。 -/
namespace PPAC.Migration.Internal.PureSyntaxListInductionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax OriginalUniversalBlock
open SyntaxRenameQuerySyntax (of_eq)

def correctAt {m} (w n b f k : Fin m) : Formula m :=
  (PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)

theorem correctAt_rename {m j} (w n b f k : Fin m) (ρ : Fin m → Fin j) :
    (correctAt w n b f k).rename ρ = correctAt (ρ w) (ρ n) (ρ b) (ρ f) (ρ k) := by
  simp only [correctAt, Formula.iff, Formula.rename, PureSyntaxTrace.arguments_rename, SyntaxMixedImageCodeSyntax.termList_rename]

def body {m} (w n : Fin m) : Formula (m+3) := correctAt (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)
def correct {m} (w n : Fin m) : Formula m := allMany 3 (body w n)

theorem body_lift {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (body w n).rename (lift 3 ρ) = body (ρ w) (ρ n) := by
  simp only [body, correctAt_rename, lift_old, lift_slot]

theorem correct_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (correct w n).rename ρ = correct (ρ w) (ρ n) := by
  simp only [correct, allMany_rename, body_lift]

theorem correct_at {m} {Γ : Context m} (w n b f k : Fin m) (hc : Derives Γ (correct w n)) :
    Derives Γ (correctAt w n b f k) := by
  have hi := at_many 3 (body w n) (SyntaxAtomSyntax.three b f k) hc
  exact of_eq (by simp only [body, correctAt_rename, assign_old, assign_slot]; rfl) hi

def allIH {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (correct w.castSucc (Fin.last m)))

theorem allIH_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (allIH w n).rename ρ = allIH (ρ w) (ρ n) := by
  simp only [allIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem allIH_at {m} {Γ : Context m} (w n t : Fin m)
    (hi : Derives Γ (allIH w n)) (ht : Derives Γ (.mem t n)) : Derives Γ (correct w t) := by
  have he : Derives Γ ((Formula.mem t n).imp (correct w t)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t hi)
  exact .impE he ht

end PPAC.Migration.Internal.PureSyntaxListInductionSyntax
