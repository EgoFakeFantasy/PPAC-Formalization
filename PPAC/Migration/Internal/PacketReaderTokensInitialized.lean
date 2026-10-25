import PPAC.Migration.Internal.PacketReaderTokensInduction
import PPAC.Migration.Internal.PacketReaderInitLiterals

/-! The actual initialized reader returns the original token list on its independent actual byte encoding. The radix, zero and unit witnesses are eliminated inside the original object derivation. -/
namespace PPAC.Migration.Internal.PacketReaderTokensInitialized
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInitSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_literals {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o n bytes p : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ ((parse w bytes p).iff (PacketReaderReturnSyntax.some w n p)) := by
  have hn := PacketTokensBytes.input_valid w n bytes he
  have hNil := StructuralNil.at_unit hZ w z o hw hz ho
  have hAcc := StructuralListTraceBase.valid_nil hZ w o hw hNil
  have hRev := StructuralListReverseNil.nil_pair hZ w o o hw hNil hNil
  have hSplice := Derives.impE
    (.conjR (StructuralListSplice.nil_iff hZ w o n n hw hNil))
    (.conjI hn (.eqRefl n))
  have hOut := PacketReaderOutputOrder.intro_output w o n n o hRev hSplice
  have hRun := PacketReaderTokensInduction.tokens hZ w B z o n bytes o n p
    hw hB hz ho hn hAcc he hOut
  have hSeeded : Derives Γ
      ((seeded w B z o bytes p).iff (PacketReaderReturnSyntax.some w n p)) := by
    simpa only [PacketReaderTokensSyntax.agreement,PacketReaderEvalSyntax.eval,seeded,seed]
      using hRun
  exact StructuralListSuffixArithmetic.iff_trans
    (PacketReaderInitLiterals.at_literals hZ w B z o bytes p hB hz ho) hSeeded

theorem at_encoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n bytes p : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ ((parse w bytes p).iff (PacketReaderReturnSyntax.some w n p)) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename])
      (OrderedPairElimination.under_two hw U)
  have he2 : Derives Δ
      (PacketTokensBytes.encoded w.castSucc.castSucc n.castSucc.castSucc bytes.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,PacketTokensBytes.encoded_rename])
      (OrderedPairElimination.under_two he U)
  let P := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNumeralSyntax.numeral 128 (Fin.last (m+2)))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P)
    (SyntaxNumerals.exists_numeral hZ2 128 w.castSucc.castSucc hw2)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 P
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 P)
  have he3 := of_eq
    (PacketTokensBytes.encoded_rename w.castSucc.castSucc n.castSucc.castSucc bytes.castSucc.castSucc Fin.castSucc)
    (under he2 P)
  have hU3 : Derives Ξ
      ((empty (Fin.last m).castSucc.castSucc).conj
        (successor (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc)) := by
    simpa only [U,StructuralListSyntax.unitWitness,Formula.raise,Formula.rename,empty_rename,successor_rename]
      using under hU P
  have hp := at_literals hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+2))
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    n.castSucc.castSucc.castSucc bytes.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc
    hw3 (.conjR hP) (.conjL hU3) (.conjR hU3) he3
  simpa only [Formula.raise,Formula.rename,parse_rename,PacketReaderReturnSyntax.some_rename] using hp

end PPAC.Migration.Internal.PacketReaderTokensInitialized
