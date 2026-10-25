import PPAC.Migration.Internal.PacketReaderInverseInitialized
import PPAC.Migration.Internal.PacketTokensBytesByte
import PPAC.Migration.Internal.PacketReaderReturnPayload

/-! Successful actual initialized reader values characterize the independent encoding exactly when the original byte bound is retained. The actual Some witness is constructed and eliminated inside the original object derivation. -/
namespace PPAC.Migration.Internal.PacketReaderInverseAccepted
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def accepted {m} (w tokens bytes : Fin m) : Formula m := .ex
  ((PacketReaderInitSyntax.parse w.castSucc bytes.castSucc (Fin.last m)).conj
    (PacketReaderReturnSyntax.some w.castSucc tokens.castSucc (Fin.last m)))

def boundedAccepted {m} (w tokens bytes : Fin m) : Formula m :=
  (PacketByteInputSyntax.byteList w bytes).conj (accepted w tokens bytes)

theorem accepted_rename {m k} (w tokens bytes : Fin m) (ρ : Fin m → Fin k) :
    (accepted w tokens bytes).rename ρ = accepted (ρ w) (ρ tokens) (ρ bytes) := by
  simp only [accepted,Formula.rename,PacketReaderInitSyntax.parse_rename,
    PacketReaderReturnSyntax.some_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem boundedAccepted_rename {m k} (w tokens bytes : Fin m) (ρ : Fin m → Fin k) :
    (boundedAccepted w tokens bytes).rename ρ = boundedAccepted (ρ w) (ρ tokens) (ρ bytes) := by
  simp only [boundedAccepted,Formula.rename,PacketByteInputSyntax.byteList_rename,accepted_rename]

theorem intro_accepted {m} {Γ : Context m} (w tokens bytes p : Fin m)
    (hParse : Derives Γ (PacketReaderInitSyntax.parse w bytes p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w tokens p)) :
    Derives Γ (accepted w tokens bytes) := by
  apply Derives.exI p
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,PacketReaderInitSyntax.parse_rename,
    PacketReaderReturnSyntax.some_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
    (.conjI hParse hSome)

theorem from_accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w tokens bytes : Fin m) (hw : Derives Γ (omega w))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w bytes))
    (hAccepted : Derives Γ (accepted w tokens bytes)) :
    Derives Γ (PacketTokensBytes.encoded w tokens bytes) := by
  let R := (PacketReaderInitSyntax.parse w.castSucc bytes.castSucc (Fin.last m)).conj
    (PacketReaderReturnSyntax.some w.castSucc tokens.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hAccepted
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hBytes1 := of_eq (PacketByteInputSyntax.byteList_rename w bytes Fin.castSucc) (under hBytes R)
  have hInverse := PacketReaderInverseInitialized.at_success hZ1 w.castSucc tokens.castSucc
    bytes.castSucc (Fin.last m) hw1 hBytes1 (.conjR hR)
  simpa only [Formula.raise,PacketTokensBytes.encoded_rename] using
    Derives.impE (.conjL hInverse) (.conjL hR)

theorem to_accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w tokens bytes : Fin m) (hw : Derives Γ (omega w))
    (hEncoded : Derives Γ (PacketTokensBytes.encoded w tokens bytes)) :
    Derives Γ (accepted w tokens bytes) := by
  have hTokens := StructuralListValidity.range w tokens
    (PacketTokensBytes.input_valid w tokens bytes hEncoded)
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (PacketReaderReturnSyntax.some w.castSucc tokens.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnPayload.some_exists hZ w tokens hw hTokens)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hEncoded1 := of_eq (PacketTokensBytes.encoded_rename w tokens bytes Fin.castSucc) (under hEncoded R)
  have hForward := PacketReaderTokensInitialized.at_encoded hZ1 w.castSucc tokens.castSucc
    bytes.castSucc (Fin.last m) hw1 hEncoded1
  have hParse := Derives.impE (.conjR hForward) (.conjR hR)
  simpa only [Formula.raise,accepted_rename] using
    intro_accepted w.castSucc tokens.castSucc bytes.castSucc (Fin.last m) hParse (.conjR hR)

theorem accepted_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w tokens bytes : Fin m) (hw : Derives Γ (omega w))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w bytes)) :
    Derives Γ ((accepted w tokens bytes).iff (PacketTokensBytes.encoded w tokens bytes)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact from_accepted (ZFContext.add hZ _) w tokens bytes (add hw _) (add hBytes _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact to_accepted (ZFContext.add hZ _) w tokens bytes (add hw _) (.hyp (Or.inl rfl))

theorem bounded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w tokens bytes : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((boundedAccepted w tokens bytes).iff (PacketTokensBytes.encoded w tokens bytes)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := boundedAccepted w tokens bytes
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    exact from_accepted (ZFContext.add hZ H) w tokens bytes (add hw H) (.conjL hH) (.conjR hH)
  · apply Derives.impI
    let H := PacketTokensBytes.encoded w tokens bytes
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ H
    exact .conjI (PacketTokensBytesByte.byte_input hZ1 w tokens bytes (add hw H) hH)
      (to_accepted hZ1 w tokens bytes (add hw H) hH)

end PPAC.Migration.Internal.PacketReaderInverseAccepted
