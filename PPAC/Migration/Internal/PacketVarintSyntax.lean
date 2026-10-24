import PPAC.Migration.Internal.PacketVarintTraceAppend
import PPAC.Migration.Internal.PacketVarintTraceBase

/-! Canonical LEB128 is a nonempty original list with an independent zero-seeded numeric trace. -/
namespace PPAC.Migration.Internal.PacketVarintSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

def canonicalAt {m} (w B n s : Fin m) : Formula m := .ex
  ((empty (Fin.last m)).conj ((foldAt w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc).conj
    (StructuralListSyntax.nilCode w.castSucc s.castSucc).neg))

def canonical {m} (w n s : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 128 (Fin.last m)).conj (canonicalAt w.castSucc (Fin.last m) n.castSucc s.castSucc))

theorem canonicalAt_rename {m k} (w B n s : Fin m) (ρ : Fin m → Fin k) :
    (canonicalAt w B n s).rename ρ = canonicalAt (ρ w) (ρ B) (ρ n) (ρ s) := by
  simp only [canonicalAt,Formula.neg,Formula.rename,empty_rename,foldAt_rename,StructuralListSyntax.nilCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem canonical_rename {m k} (w n s : Fin m) (ρ : Fin m → Fin k) :
    (canonical w n s).rename ρ = canonical (ρ w) (ρ n) (ρ s) := by
  simp only [canonical,Formula.rename,SyntaxNumeralSyntax.numeral_rename,canonicalAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_at {m} {Γ : Context m} (w B n s z : Fin m) (hz : Derives Γ (empty z))
    (hf : Derives Γ (foldAt w B s z n)) (hs : Derives Γ (StructuralListSyntax.nilCode w s).neg) : Derives Γ (canonicalAt w B n s) := by
  apply Derives.exI z
  exact of_eq (by simp only [Formula.instantiate,Formula.neg,Formula.rename,empty_rename,foldAt_rename,StructuralListSyntax.nilCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hz (.conjI hf hs))

theorem intro_actual {m} {Γ : Context m} (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hc : Derives Γ (canonicalAt w B n s)) : Derives Γ (canonical w n s) := by
  apply Derives.exI B
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,canonicalAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hB hc)

end PPAC.Migration.Internal.PacketVarintSyntax
