import PPAC.Migration.Internal.PacketVarintPrefixRecursionSyntax

/-! A given actual singleton list identifies the terminal byte output and the original arithmetic cell. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixSmall
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintPrefixRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n s t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hc : Derives Γ (PacketVarintCanonicalRecursionSyntax.smallCase w B n s)) (hb : Derives Γ (PacketBytesTraceSyntax.bytes w s t a)) :
    Derives Γ (smallCase w B C n t a) := by
  have hn := StructuralListTraceOrder.member_member hZ w n B hw (SyntaxNumerals.range hZ 128 w B hw hB) (.conjL hc)
  let E := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) s.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (.conjR hc)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC E)
  have hb1 := of_eq (PacketBytesTraceSyntax.bytes_rename w s t a Fin.castSucc) (under hb E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ha := PacketBytesCons.singleton hZ1 w.castSucc n.castSucc (Fin.last m) s.castSucc t.castSucc a.castSucc hw1 (under hn E) (.conjL hE) (.conjR hE) hb1
  have harith := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc C.castSucc n.castSucc t.castSucc a.castSucc hw1 hC1)) ha
  have hout : Derives Δ (smallCase w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc a.castSucc) := .conjI (under (.conjL hc) E) harith
  simpa only [Formula.raise,smallCase_rename] using hout

end PPAC.Migration.Internal.PacketVarintPrefixSmall
