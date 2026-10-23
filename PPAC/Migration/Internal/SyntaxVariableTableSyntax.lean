import PPAC.Migration.Internal.SyntaxVariableImageFields
import PPAC.Migration.Internal.SyntaxIdentityUnique
import PPAC.Migration.Internal.SyntaxFreeShiftFiber

/-! 实际恒等/后移变量项码表；隐藏索引图见证属于对象量词。 -/
namespace PPAC.Migration.Internal.SyntaxVariableTableSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxTermSyntax
open SyntaxVariableImageSyntax (mapped mapped_rename)
open SyntaxIdentityMapSyntax (identityMap identityMap_rename)
open SyntaxFreeShiftSyntax (shiftMap shiftMap_rename)

def identityBody {m} (bound : Bool) (w c d f : Fin m) : Formula (m+1) :=
  (identityMap w.castSucc (limit bound c.castSucc d.castSucc) (Fin.last m)).conj
    (mapped bound w.castSucc (Fin.last m) (limit bound c.castSucc d.castSucc) c.castSucc d.castSucc f.castSucc)

def identity {m} (bound : Bool) (w c d f : Fin m) : Formula m := .ex (identityBody bound w c d f)

def shiftedBody {m} (bound : Bool) (w a c d f : Fin m) : Formula (m+1) :=
  (shiftMap w.castSucc a.castSucc (limit bound c.castSucc d.castSucc) (Fin.last m)).conj
    (mapped bound w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc f.castSucc)

def shifted {m} (bound : Bool) (w a c d f : Fin m) : Formula m := .ex (shiftedBody bound w a c d f)

def existsIdentity {m} (bound : Bool) (w c d : Fin m) : Formula m := .ex
  (identity bound w.castSucc c.castSucc d.castSucc (Fin.last m))

def existsShifted {m} (bound : Bool) (w a c d : Fin m) : Formula m := .ex
  (shifted bound w.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m))

theorem identity_rename {m k} (bound : Bool) (w c d f : Fin m) (ρ : Fin m → Fin k) :
    (identity bound w c d f).rename ρ = identity bound (ρ w) (ρ c) (ρ d) (ρ f) := by
  simp only [identity, identityBody, Formula.rename, identityMap_rename, mapped_rename, limit_map,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem shifted_rename {m k} (bound : Bool) (w a c d f : Fin m) (ρ : Fin m → Fin k) :
    (shifted bound w a c d f).rename ρ = shifted bound (ρ w) (ρ a) (ρ c) (ρ d) (ρ f) := by
  simp only [shifted, shiftedBody, Formula.rename, shiftMap_rename, mapped_rename, limit_map,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsIdentity_rename {m k} (bound : Bool) (w c d : Fin m) (ρ : Fin m → Fin k) :
    (existsIdentity bound w c d).rename ρ = existsIdentity bound (ρ w) (ρ c) (ρ d) := by
  simp only [existsIdentity, Formula.rename, identity_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsShifted_rename {m k} (bound : Bool) (w a c d : Fin m) (ρ : Fin m → Fin k) :
    (existsShifted bound w a c d).rename ρ = existsShifted bound (ρ w) (ρ a) (ρ c) (ρ d) := by
  simp only [existsShifted, Formula.rename, shifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_identity {m} {Γ : Context m} (bound : Bool) (w c d f r : Fin m)
    (hr : Derives Γ (identityMap w (limit bound c d) r))
    (hf : Derives Γ (mapped bound w r (limit bound c d) c d f)) : Derives Γ (identity bound w c d f) := by
  apply Derives.exI r
  exact of_eq (by simp only [identityBody, Formula.instantiate, Formula.rename, identityMap_rename, mapped_rename,
    limit_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hf)

theorem intro_shifted {m} {Γ : Context m} (bound : Bool) (w a c d f r : Fin m)
    (hr : Derives Γ (shiftMap w a (limit bound c d) r))
    (hf : Derives Γ (mapped bound w r a c d f)) : Derives Γ (shifted bound w a c d f) := by
  apply Derives.exI r
  exact of_eq (by simp only [shiftedBody, Formula.instantiate, Formula.rename, shiftMap_rename, mapped_rename,
    limit_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hf)
end PPAC.Migration.Internal.SyntaxVariableTableSyntax
