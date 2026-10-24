import PPAC.Migration.Internal.SyntaxNumeralAddition

/-! Actual internal 128+128=256 yields the shifted-byte bound used by real token execution. -/
namespace PPAC.Migration.Internal.PacketTokenByteBounds
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic

theorem radix_sum {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) : Derives Γ (NaturalAdditionSyntax.sum w B B C) :=
  SyntaxNumeralAddition.sum_at hZ 128 128 w B B C hw hB hB hC

theorem small_digit_byte {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C d : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hd : Derives Γ (.mem d B)) : Derives Γ (.mem d C) :=
  PacketDivisionDescentOrder.member_below hZ w d B C hw (SyntaxNumerals.range hZ 256 w C hw hC) hd
    (.disjR (SyntaxNumerals.less hZ 128 256 (by decide) B C hB hC))

theorem shifted_digit_byte {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C d y : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hd : Derives Γ (.mem d B))
    (hy : Derives Γ (NaturalAdditionSyntax.sum w d B y)) : Derives Γ (.mem y C) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hdN := StructuralListTraceOrder.member_member hZ w d B hw hBN hd
  exact NaturalAdditionMonotone.strict_monotone hZ w d B B y C hw hdN hBN hBN hy (radix_sum hZ w B C hw hB hC) hd

theorem quotient_nonzero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hn : Derives Γ (Formula.mem n B).neg) : Derives Γ (empty q).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.impE (add (.conjL (PacketDivisionDescentCore.terminal_iff hZ w B d q n hw ha)) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenByteBounds
