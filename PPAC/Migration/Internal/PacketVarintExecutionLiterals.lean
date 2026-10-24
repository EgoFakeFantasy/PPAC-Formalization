import PPAC.Migration.Internal.PacketVarintExecutionInduction

/-! Internal 128 and 256 are obtained and eliminated; no numeral or recursive IH premise remains. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionLiterals
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax PacketVarintExecutionSyntax PacketVarintExecutionInduction
open SyntaxRenameQuerySyntax (of_eq)

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allProperties w) := by
  let P := PacketAffineLiteralSyntax.frame false w.castSucc (Fin.last m)
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 128 w hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  let Q := PacketAffineLiteralSyntax.frame true w.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (SyntaxNumerals.exists_numeral hZ1 256 w.castSucc hw1)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hP2 := of_eq (PacketAffineLiteralSyntax.frame_rename false w.castSucc (Fin.last m) Fin.castSucc) (under hP Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  simpa only [Formula.raise,allProperties_rename] using all_properties_at hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjR hP2) (.conjR hQ)

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have he : Derives Γ ((Formula.mem n w).imp (property w n)) := by
    simpa only [allProperties,Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using Derives.allE n (all_properties hZ w hw)
  exact .impE he hn

theorem exists_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsList w n) :=
  .conjL (at_code hZ w n hw hn)

theorem byte_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (canonical w n s)) : Derives Γ (PacketByteInputSyntax.byteList w s) :=
  domain_at w n s (at_code hZ w n hw (.conjL (PacketVarintDomain.domain w n s hc))) hc

theorem list_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s t : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (canonical w n s)) (ht : Derives Γ (canonical w n t)) : Derives Γ (.equal s t) :=
  unique_at w n s t (at_code hZ w n hw (.conjL (PacketVarintDomain.domain w n s hs))) hs ht

end PPAC.Migration.Internal.PacketVarintExecutionLiterals
