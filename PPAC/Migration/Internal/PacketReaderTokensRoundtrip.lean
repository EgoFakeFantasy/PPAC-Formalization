import PPAC.Migration.Internal.PacketReaderTokensInitialized

/-! Every actual internal token list has one actual encoded byte list, and the initialized reader has the exact Some result on every object return candidate. Both candidate quantifiers remain inside the original object derivation. -/
namespace PPAC.Migration.Internal.PacketReaderTokensRoundtrip
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def allReturns {m} (w n bytes : Fin m) : Formula m := .all
  ((PacketReaderInitSyntax.parse w.castSucc bytes.castSucc (Fin.last m)).iff
    (PacketReaderReturnSyntax.some w.castSucc n.castSucc (Fin.last m)))

def completeBody {m} (w n : Fin m) : Formula (m+1) :=
  ((Formula.mem (Fin.last m) w.castSucc).conj
    (PacketTokensBytes.encoded w.castSucc n.castSucc (Fin.last m))).conj
  ((PacketTokensBytes.uniqueAt w.castSucc n.castSucc (Fin.last m)).conj
    (allReturns w.castSucc n.castSucc (Fin.last m)))

def complete {m} (w n : Fin m) : Formula m := .ex (completeBody w n)

theorem allReturns_rename {m k} (w n bytes : Fin m) (ρ : Fin m → Fin k) :
    (allReturns w n bytes).rename ρ = allReturns (ρ w) (ρ n) (ρ bytes) := by
  simp only [allReturns,Formula.iff,Formula.rename,PacketReaderInitSyntax.parse_rename,
    PacketReaderReturnSyntax.some_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem complete_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (complete w n).rename ρ = complete (ρ w) (ρ n) := by
  simp only [complete,completeBody,Formula.rename,PacketTokensBytes.encoded_rename,
    PacketTokensBytes.uniqueAt_rename,allReturns_rename,Formula.liftRen,
    Fin.lastCases_last,Fin.lastCases_castSucc]

theorem all_returns {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n bytes : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ (allReturns w n bytes) := by
  apply Derives.allI
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) :=
    of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have he1 : Derives (Context.image Formula.raise Γ)
      (PacketTokensBytes.encoded w.castSucc n.castSucc bytes.castSucc) :=
    of_eq (PacketTokensBytes.encoded_rename w n bytes Fin.castSucc)
      (Derives.rename Fin.castSucc he)
  exact PacketReaderTokensInitialized.at_encoded (ZFContext.rename hZ Fin.castSucc)
    w.castSucc n.castSucc bytes.castSucc (Fin.last m) hw1 he1

theorem intro_complete {m} {Γ : Context m} (w n bytes : Fin m)
    (hb : Derives Γ (.mem bytes w))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes))
    (hu : Derives Γ (PacketTokensBytes.uniqueAt w n bytes))
    (hr : Derives Γ (allReturns w n bytes)) : Derives Γ (complete w n) := by
  apply Derives.exI bytes
  exact of_eq (by
    simp only [completeBody,Formula.instantiate,Formula.rename,
      PacketTokensBytes.encoded_rename,PacketTokensBytes.uniqueAt_rename,
      allReturns_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
    (.conjI (.conjI hb he) (.conjI hu hr))

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) :
    Derives Γ (complete w n) := by
  let R := PacketTokensBytes.fiberBody w n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketTokensBytes.exists_unique hZ w n hw hn)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hRet := all_returns hZ1 w.castSucc n.castSucc (Fin.last m) hw1
    (.conjR (.conjL hR))
  have hout := intro_complete w.castSucc n.castSucc (Fin.last m)
    (.conjL (.conjL hR)) (.conjR (.conjL hR)) (.conjR hR) hRet
  simpa only [Formula.raise,complete_rename] using hout

end PPAC.Migration.Internal.PacketReaderTokensRoundtrip
