import PPAC.Migration.Internal.PacketBytesExecutionTransport

/-! Original actual 256 cells have an independent byte domain, total output and uniqueness; all literals are eliminated. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionAffine
open Source SourceAlgebra SourceLogic OmegaSyntax PacketBytesTraceSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def cellData {m} (w h u a : Fin m) : Formula m := (byte h).conj ((Formula.mem u w).conj (.mem a w))

def existsCell {m} (w h u : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (PacketAffineAcceptedSyntax.accepted true w.castSucc h.castSucc u.castSucc (Fin.last m)))

theorem cellData_rename {m k} (w h u a : Fin m) (ρ : Fin m → Fin k) :
    (cellData w h u a).rename ρ = cellData (ρ w) (ρ h) (ρ u) (ρ a) := by
  simp only [cellData,Formula.rename,byte_rename]

theorem existsCell_rename {m k} (w h u : Fin m) (ρ : Fin m → Fin k) :
    (existsCell w h u).rename ρ = existsCell (ρ w) (ρ h) (ρ u) := by
  simp only [existsCell,Formula.rename,PacketAffineAcceptedSyntax.accepted_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_cell {m} {Γ : Context m} (w h u a : Fin m) (ha : Derives Γ (.mem a w))
    (hc : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (existsCell w h u) := by
  apply Derives.exI a
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,PacketAffineAcceptedSyntax.accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI ha hc)

theorem data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h u a : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (cellData w h u a) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w h u a Fin.castSucc) (under hc R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc (Fin.last m) h.castSucc u.castSucc a.castSucc hw1 (.conjR hR))) hc1
  have hb := intro_byte (Fin.last m) h.castSucc (.conjR hR) (PacketAffineCore.digit_guard _ _ _ _ _ ha)
  have hout : Derives Δ (cellData w.castSucc h.castSucc u.castSucc a.castSucc) := .conjI hb
    (.conjI (PacketAffineCore.tail_guard _ _ _ _ _ ha) (PacketAffineCore.output_guard _ _ _ _ _ ha))
  simpa only [Formula.raise,cellData_rename] using hout

theorem exists_cell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h u : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (byte h)) (hu : Derives Γ (.mem u w)) : Derives Γ (existsCell w h u) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let ΓR := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hb1 := of_eq (byte_rename h Fin.castSucc) (under hb R)
  have hR : Derives ΓR R := .hyp (Or.inl rfl)
  have hh := PacketByteInputBridge.byte_at hZ1 (Fin.last m) h.castSucc (.conjR hR) hb1
  have hex := PacketAffineCore.exists_value hZ1 w.castSucc (Fin.last m) h.castSucc u.castSucc hw1 (.conjL hR) hh (under hu R)
  let A := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (PacketAffineSyntax.affine w.castSucc.castSucc (Fin.last m).castSucc h.castSucc.castSucc u.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add A (Context.image Formula.raise ΓR)
  apply Derives.exE (p := A) hex
  have hZ2 := ZFContext.under hZ1 A
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 A)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 (Fin.last m) Fin.castSucc) (under (.conjR hR) A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff hZ2 true w.castSucc.castSucc (Fin.last m).castSucc h.castSucc.castSucc u.castSucc.castSucc (Fin.last (m+1)) hw2 hC2)) (.conjR hA)
  simpa only [Formula.raise,existsCell_rename] using intro_cell w.castSucc.castSucc h.castSucc.castSucc u.castSucc.castSucc (Fin.last (m+1)) (.conjL hA) hc

theorem unique_cell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h u a b : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) (hb : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u b)) : Derives Γ (.equal a b) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have ha1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w h u a Fin.castSucc) (under ha R)
  have hb1 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true w h u b Fin.castSucc) (under hb R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have h0 := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc (Fin.last m) h.castSucc u.castSucc a.castSucc hw1 (.conjR hR))) ha1
  have h1 := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ1 true w.castSucc (Fin.last m) h.castSucc u.castSucc b.castSucc hw1 (.conjR hR))) hb1
  exact PacketAffineCore.unique hZ1 w.castSucc (Fin.last m) h.castSucc u.castSucc a.castSucc b.castSucc hw1 h0 h1

theorem bytes_input_natural {m} {Γ : Context m} (w n t a : Fin m) (hb : Derives Γ (bytes w n t a)) : Derives Γ (.mem n w) :=
  StructuralListValidity.range _ _ (.conjL (PacketBytesLaws.domain w n t a hb))

end PPAC.Migration.Internal.PacketBytesExecutionAffine
