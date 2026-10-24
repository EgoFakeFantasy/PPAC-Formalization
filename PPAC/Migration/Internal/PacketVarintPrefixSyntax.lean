import PPAC.Migration.Internal.PacketVarintCellLaws

/-! An independent canonical byte list followed by the actual byte fold specifies the exact remaining numeric tail. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixSyntax
open Source SourceAlgebra SourceLogic PacketVarintSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w n t a : Fin m) : Formula (m+1) :=
  (canonical w.castSucc n.castSucc (Fin.last m)).conj (PacketBytesTraceSyntax.bytes w.castSucc (Fin.last m) t.castSucc a.castSucc)

def prefixCode {m} (w n t a : Fin m) : Formula m := .ex (body w n t a)

theorem prefixCode_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (prefixCode w n t a).rename ρ = prefixCode (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [prefixCode,body,Formula.rename,canonical_rename,PacketBytesTraceSyntax.bytes_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_prefix {m} {Γ : Context m} (w n t a s : Fin m) (hc : Derives Γ (canonical w n s))
    (hb : Derives Γ (PacketBytesTraceSyntax.bytes w s t a)) : Derives Γ (prefixCode w n t a) := by
  apply Derives.exI s
  exact of_eq (by simp only [body,Formula.instantiate,Formula.rename,canonical_rename,PacketBytesTraceSyntax.bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hc hb)

end PPAC.Migration.Internal.PacketVarintPrefixSyntax
