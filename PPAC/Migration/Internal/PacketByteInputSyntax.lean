import PPAC.Migration.Internal.PacketBytesRecursionLaws
import PPAC.Migration.Internal.ObjectStructuralListEncode

/-! Independent valid-byte inputs use the original complete Fields graph and its real byte range. -/
namespace PPAC.Migration.Internal.PacketByteInputSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax StructuralListLengthSyntax StructuralListFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)

def bounds {m} (w C n l : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).imp
    ((field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp (.mem (Fin.last (m+1)) C.castSucc.castSucc))))

def lengthCase {m} (w C n l : Fin m) : Formula m := (hasLength w n l).conj (bounds w C n l)

def lengthExists {m} (w C n : Fin m) : Formula m := .ex (lengthCase w.castSucc C.castSucc n.castSucc (Fin.last m))

def inputBody {m} (w C n : Fin m) : Formula (m+2) :=
  (StructuralListEncodeSyntax.encoding (old 2 w) (slot 2 1) (slot 2 0) (old 2 n)).conj
    (SequenceSyntax.bounded (slot 2 1) (old 2 C))

def inputAt {m} (w C n : Fin m) : Formula m := existsMany 2 (inputBody w C n)

def byte {m} (h : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (.mem h.castSucc (Fin.last m)))

def byteList {m} (w n : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (inputAt w.castSucc (Fin.last m) n.castSucc))

theorem bounds_rename {m k} (w C n l : Fin m) (ρ : Fin m → Fin k) :
    (bounds w C n l).rename ρ = bounds (ρ w) (ρ C) (ρ n) (ρ l) := by
  simp only [bounds,Formula.rename,field_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lengthCase_rename {m k} (w C n l : Fin m) (ρ : Fin m → Fin k) :
    (lengthCase w C n l).rename ρ = lengthCase (ρ w) (ρ C) (ρ n) (ρ l) := by
  simp only [lengthCase,Formula.rename,hasLength_rename,bounds_rename]

theorem lengthExists_rename {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (lengthExists w C n).rename ρ = lengthExists (ρ w) (ρ C) (ρ n) := by
  simp only [lengthExists,Formula.rename,lengthCase_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem inputBody_lift {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (inputBody w C n).rename (lift 2 ρ) = inputBody (ρ w) (ρ C) (ρ n) := by
  simp only [inputBody,Formula.rename,StructuralListEncodeSyntax.encoding_rename,SequenceSyntax.bounded_rename,lift_old,lift_slot]

theorem inputAt_rename {m k} (w C n : Fin m) (ρ : Fin m → Fin k) :
    (inputAt w C n).rename ρ = inputAt (ρ w) (ρ C) (ρ n) := by
  simp only [inputAt,existsMany_rename,inputBody_lift]

theorem byte_rename {m k} (h : Fin m) (ρ : Fin m → Fin k) : (byte h).rename ρ = byte (ρ h) := by
  simp only [byte,Formula.rename,SyntaxNumeralSyntax.numeral_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem byteList_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (byteList w n).rename ρ = byteList (ρ w) (ρ n) := by
  simp only [byteList,Formula.rename,SyntaxNumeralSyntax.numeral_rename,inputAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem bounds_at {m} {Γ : Context m} (w C n l i y : Fin m) (hb : Derives Γ (bounds w C n l))
    (hi : Derives Γ (.mem i l)) (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y C) := by
  have h : Derives Γ ((Formula.mem i l).imp ((field w n i y).imp (.mem y C))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,field_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE y (Derives.allE i hb))
  exact .impE (.impE h hi) hy

theorem intro_length {m} {Γ : Context m} (w C n l : Fin m) (hl : Derives Γ (hasLength w n l))
    (hb : Derives Γ (bounds w C n l)) : Derives Γ (lengthExists w C n) := by
  apply Derives.exI l
  exact of_eq (by simp only [Formula.instantiate,lengthCase_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]; rfl) (.conjI hl hb)

theorem intro_input {m} {Γ : Context m} (w C n l f : Fin m) (he : Derives Γ (StructuralListEncodeSyntax.encoding w f l n))
    (hb : Derives Γ (SequenceSyntax.bounded f C)) : Derives Γ (inputAt w C n) := by
  apply HornBinderRules.intro_many 2 (inputBody w C n) (SyntaxAtomSyntax.two l f)
  exact of_eq (by simp only [inputBody,Formula.rename,StructuralListEncodeSyntax.encoding_rename,SequenceSyntax.bounded_rename,assign_old,assign_slot]; rfl) (.conjI he hb)

theorem intro_byte {m} {Γ : Context m} (C h : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hh : Derives Γ (.mem h C)) : Derives Γ (byte h) := by
  apply Derives.exI C
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hC hh)

theorem intro_actual {m} {Γ : Context m} (w C n : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hi : Derives Γ (inputAt w C n)) : Derives Γ (byteList w n) := by
  apply Derives.exI C
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,inputAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hC hi)

end PPAC.Migration.Internal.PacketByteInputSyntax
