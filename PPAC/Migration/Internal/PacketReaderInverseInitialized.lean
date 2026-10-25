import PPAC.Migration.Internal.PacketReaderInverseInduction
import PPAC.Migration.Internal.PacketReaderTokensInitialized
import PPAC.Migration.Internal.PacketReaderOutputBackward

/-! Successful actual initialized parsing of bounded input is equivalent to the independent actual token encoding. All radix, zero and unit witnesses are eliminated inside original object derivations; packet AST and internal consistency remain separate obligations. -/
namespace PPAC.Migration.Internal.PacketReaderInverseInitialized
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInitSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem encoded_input_subst {m} {Γ : Context m} (w n t bytes : Fin m)
    (he : Derives Γ (.equal n t)) (hn : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ (PacketTokensBytes.encoded w t bytes) := by
  let P := PacketTokensBytes.encoded w.castSucc (Fin.last m) bytes.castSucc
  have h0 : P.instantiate n = PacketTokensBytes.encoded w n bytes := by
    simp only [P,Formula.instantiate,PacketTokensBytes.encoded_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate t = PacketTokensBytes.encoded w t bytes := by
    simp only [P,Formula.instantiate,PacketTokensBytes.encoded_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hn))

theorem at_literals {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o tokens bytes p : Fin m) (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w bytes))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w tokens p)) :
    Derives Γ ((parse w bytes p).iff (PacketTokensBytes.encoded w tokens bytes)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := parse w bytes p
    have hZ1 := ZFContext.add hZ H
    have hParse : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hLiteral := PacketReaderInitLiterals.at_literals hZ1 w B z o bytes p
      (add hB H) (add hz H) (add ho H)
    have hSeeded := Derives.impE (.conjL hLiteral) hParse
    have hEval : Derives (Context.add H Γ)
        (PacketReaderEvalSyntax.eval w B z o bytes z o o p) := by
      simpa only [seeded,seed,PacketReaderEvalSyntax.eval] using hSeeded
    have hInverse := PacketReaderInverseInduction.inverse hZ1 w B z o bytes o tokens p
      (add hw H) (add hB H) (add hz H) (add ho H) (add hBytes H) hEval (add hSome H)
    let R := (PacketTokensBytes.encoded w.castSucc (Fin.last m) bytes.castSucc).conj
      (PacketReaderOutputOrder.output w.castSucc o.castSucc (Fin.last m) tokens.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) hInverse
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 R
    have hw2 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hz2 := of_eq (empty_rename z Fin.castSucc) (under (add hz H) R)
    have ho2 := of_eq (successor_rename o z Fin.castSucc) (under (add ho H) R)
    have hNil := StructuralNil.at_unit hZ2 w.castSucc z.castSucc o.castSucc hw2 hz2 ho2
    have hOutput := PacketReaderOutputBackward.nil_accumulator hZ2 w.castSucc o.castSucc
      (Fin.last m) tokens.castSucc hw2 hNil
    have hEqual := Derives.conjR (Derives.impE (.conjL hOutput) (.conjR hR))
    simpa only [Formula.raise,PacketTokensBytes.encoded_rename] using
      encoded_input_subst w.castSucc (Fin.last m) tokens.castSucc bytes.castSucc hEqual (.conjL hR)
  · apply Derives.impI
    let H := PacketTokensBytes.encoded w tokens bytes
    have hEncoded : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hForward := PacketReaderTokensInitialized.at_encoded (ZFContext.add hZ H)
      w tokens bytes p (add hw H) hEncoded
    exact .impE (.conjR hForward) (add hSome H)

theorem at_success {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w tokens bytes p : Fin m) (hw : Derives Γ (omega w))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w bytes))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w tokens p)) :
    Derives Γ ((parse w bytes p).iff (PacketTokensBytes.encoded w tokens bytes)) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename]) (OrderedPairElimination.under_two hw U)
  have hBytes2 : Derives Δ (PacketByteInputSyntax.byteList w.castSucc.castSucc bytes.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,PacketByteInputSyntax.byteList_rename])
      (OrderedPairElimination.under_two hBytes U)
  have hSome2 : Derives Δ (PacketReaderReturnSyntax.some w.castSucc.castSucc tokens.castSucc.castSucc p.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,PacketReaderReturnSyntax.some_rename])
      (OrderedPairElimination.under_two hSome U)
  let P := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNumeralSyntax.numeral 128 (Fin.last (m+2)))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ2 128 w.castSucc.castSucc hw2)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 P
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 P)
  have hBytes3 := of_eq (PacketByteInputSyntax.byteList_rename w.castSucc.castSucc bytes.castSucc.castSucc Fin.castSucc)
    (under hBytes2 P)
  have hSome3 := of_eq (PacketReaderReturnSyntax.some_rename w.castSucc.castSucc tokens.castSucc.castSucc p.castSucc.castSucc Fin.castSucc)
    (under hSome2 P)
  have hU3 : Derives Ξ ((empty (Fin.last m).castSucc.castSucc).conj
      (successor (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc)) := by
    simpa only [U,StructuralListSyntax.unitWitness,Formula.raise,Formula.rename,empty_rename,successor_rename]
      using under hU P
  have hResult := at_literals hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+2))
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    tokens.castSucc.castSucc.castSucc bytes.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc
    hw3 (.conjR hP) (.conjL hU3) (.conjR hU3) hBytes3 hSome3
  simpa only [Formula.raise,Formula.rename,parse_rename,PacketTokensBytes.encoded_rename] using hResult

end PPAC.Migration.Internal.PacketReaderInverseInitialized
