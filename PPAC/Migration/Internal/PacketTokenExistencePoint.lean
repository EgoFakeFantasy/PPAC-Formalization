import PPAC.Migration.Internal.PacketTokenExistenceSyntax

/-! Actual small and recursive token outputs are internally constructed from real affine runs. -/
namespace PPAC.Migration.Internal.PacketTokenExistencePoint
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenAcceptedSyntax PacketTokenExistenceSyntax
open PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)

theorem small_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (.mem n B)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsOutput w n t) := by
  have hbyte := PacketTokenByteBounds.small_digit_byte hZ w B C n hw hB hC hn
  have he := PacketAffineCore.exists_value hZ w C n t hw (SyntaxNumerals.range hZ 256 w C hw hC) hbyte ht
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (affine w.castSucc C.castSucc n.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hn1 : Derives Δ (.mem n.castSucc B.castSucc) := under hn R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjR (PacketTokenArithmeticProperties.accepted_small_iff hZ1 w.castSucc B.castSucc C.castSucc
    n.castSucc t.castSucc (Fin.last m) hw1 hB1 hC1 hn1)) (.conjR hR)
  exact of_eq (existsOutput_rename w n t Fin.castSucc).symm (intro_output w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjL hR) ha)

theorem step_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t u y : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (h0 : Derives Γ (affine w B d q n))
    (hq : Derives Γ (empty q).neg) (hs : Derives Γ (NaturalAdditionSyntax.sum w d B y))
    (hu : Derives Γ (accepted w q t u)) : Derives Γ (existsOutput w n t) := by
  have hbyte := PacketTokenByteBounds.shifted_digit_byte hZ w B C d y hw hB hC (digit_guard _ _ _ _ _ h0) hs
  have huN := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three q t u)
    (PacketTokenAcceptedNatural.accepted_environment hZ w q t u hw hu) 2
  have he := PacketAffineCore.exists_value hZ w C y u hw (SyntaxNumerals.range hZ 256 w C hw hC) hbyte huN
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (affine w.castSucc C.castSucc y.castSucc u.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have h01 := of_eq (affine_rename w B d q n Fin.castSucc) (under h0 R)
  have hq1 : Derives Δ (empty q.castSucc).neg := of_eq (by simp only [Formula.raise,Formula.neg,Formula.rename,empty_rename]) (under hq R)
  have hs1 := of_eq (NaturalAdditionSyntax.sum_rename w d B y Fin.castSucc) (under hs R)
  have hu1 := of_eq (accepted_rename w q t u Fin.castSucc) (under hu R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hl := PacketTokenArithmeticSyntax.intro_large w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc (Fin.last m)
    d.castSucc q.castSucc u.castSucc y.castSucc h01 hq1 hs1 hu1 (.conjR hR)
  have ha := Derives.impE (.conjR (PacketTokenArithmeticEquation.accepted_iff hZ1 w.castSucc B.castSucc C.castSucc
    n.castSucc t.castSucc (Fin.last m) hw1 hB1 hC1)) (.disjR hl)
  exact of_eq (existsOutput_rename w n t Fin.castSucc).symm (intro_output w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjL hR) ha)

theorem large_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (h0 : Derives Γ (affine w B d q n))
    (hn : Derives Γ (Formula.mem n B).neg) (hp : Derives Γ (property w q)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsOutput w n t) := by
  have hq := PacketTokenByteBounds.quotient_nonzero hZ w B d q n hw h0 hn
  have he := property_at w q t hp ht
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (accepted w.castSucc q.castSucc t.castSucc (Fin.last m))
  let ΓR := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have h01 := of_eq (affine_rename w B d q n Fin.castSucc) (under h0 R)
  have hq1 : Derives ΓR (empty q.castSucc).neg := of_eq (by simp only [Formula.raise,Formula.neg,Formula.rename,empty_rename]) (under hq R)
  have hR : Derives ΓR R := .hyp (Or.inl rfl)
  have hy := ZFArithmetic.add_exists hZ1 w.castSucc d.castSucc B.castSucc hw1 (digit_natural hZ1 _ _ _ _ _ hw1 h01) (radix_guard _ _ _ _ _ h01)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc d.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise ΓR)
  apply Derives.exE (p := Y) hy
  have hZ2 := ZFContext.under hZ1 Y
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B.castSucc Fin.castSucc) (under hB1 Y)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C.castSucc Fin.castSucc) (under hC1 Y)
  have h02 := of_eq (affine_rename w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc Fin.castSucc) (under h01 Y)
  have hq2 : Derives Δ (empty q.castSucc.castSucc).neg := of_eq (by simp only [Formula.raise,Formula.neg,Formula.rename,empty_rename]) (under hq1 Y)
  have hu2 := of_eq (accepted_rename w.castSucc q.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) Y)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have ho := step_values hZ2 w.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc d.castSucc.castSucc
    q.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB2 hC2 h02 hq2 (.conjR hY) hu2
  simpa only [Formula.raise,existsOutput_rename] using ho

end PPAC.Migration.Internal.PacketTokenExistencePoint
