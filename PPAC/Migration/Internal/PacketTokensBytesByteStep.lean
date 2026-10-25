import PPAC.Migration.Internal.PacketTokensBytesBytePoint

/-! Actual encoded-input validity and genuine Cons code membership close the byte-bound step on every internal token list. -/
namespace PPAC.Migration.Internal.PacketTokensBytesByteStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokensBytesByteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) : Derives Γ (PacketByteInputSyntax.byteList w bytes) := by
  have hn := PacketTokensBytes.input_valid w n bytes he
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w n hw hn)
  · exact PacketTokensBytesBytePoint.nil_point (ZFContext.add hZ _) _ _ _ (add hw _) (.hyp (Or.inl rfl)) (add he _)
  · let P := StructuralListDecodeSyntax.tailCase w n
    let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) n.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) R
    have hx := StructuralListValidity.range _ _ (.conjL hR)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
    let Ξ := Context.add H (Context.image Formula.raise Δ)
    apply Derives.exE (p := H) (.conjR hR)
    have hH : Derives Ξ H := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 H
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under (add hw P) R) H)
    have hi2 : Derives Ξ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,earlier_rename]) (under (under (add hi P) R) H)
    have he2 : Derives Ξ (PacketTokensBytes.encoded w.castSucc.castSucc n.castSucc.castSucc bytes.castSucc.castSucc) := of_eq (by simp only [Formula.raise,PacketTokensBytes.encoded_rename]) (under (under (add he P) R) H)
    have hxN : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hx H
    have hBelow := Derives.conjR (StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjL hH) hxN (.conjR hH))
    have hIH := earlier_at w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc hi2 hxN hBelow
    simpa only [Formula.raise,PacketByteInputSyntax.byteList_rename] using
      PacketTokensBytesBytePoint.cons_point hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc bytes.castSucc.castSucc hw2 (.conjL hH) hxN (.conjR hH) hIH he2

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.impI
  let E := PacketTokensBytes.encoded w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hi1 := of_eq (earlier_rename w n Fin.castSucc) (under hi E)
  exact from_earlier_point hZ1 w.castSucc n.castSucc (Fin.last m) hw1 hi1 (.hyp (Or.inl rfl) : Derives Δ E)

end PPAC.Migration.Internal.PacketTokensBytesByteStep
