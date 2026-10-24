import PPAC.Migration.Internal.ObjectPacketTokenArithmetic

/-! External finite numeral indices construct object certificates; runtime values remain arbitrary internal objects. -/
namespace PPAC.Migration.Internal.SyntaxNumeralAddition
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem sum_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i j : Nat) (w a b c : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (numeral i a)) (hb : Derives Γ (numeral j b))
    (hc : Derives Γ (numeral (i+j) c)) : Derives Γ (sum w a b c) := by
  induction j generalizing m with
  | zero =>
    have he := SyntaxNumerals.unique hZ i a c ha hc
    exact NaturalAdditionSyntax.output_subst w a b a c he (add_zero hZ w a b hw (SyntaxNumerals.range hZ i w a hw ha) hb)
  | succ j ih =>
    let B := (numeral j (Fin.last m)).conj (successor b.castSucc (Fin.last m))
    let ΓB := Context.add B (Context.image Formula.raise Γ)
    apply eliminate_succ j b _ hb
    have hc1 := of_eq (numeral_rename (i+(j+1)) c Fin.castSucc) (under hc B)
    let C := (numeral (i+j) (Fin.last (m+1))).conj (successor c.castSucc.castSucc (Fin.last (m+1)))
    let Δ := Context.add C (Context.image Formula.raise ΓB)
    apply eliminate_succ (i+j) c.castSucc _ hc1
    have hZ2 := ZFContext.under (ZFContext.under hZ B) C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw B) C)
    have ha2 : Derives Δ (numeral i a.castSucc.castSucc) := of_eq (by simp only [Formula.raise,numeral_rename]) (under (under ha B) C)
    have hB : Derives ΓB B := .hyp (Or.inl rfl)
    have hB2 : Derives Δ ((numeral j (Fin.last m).castSucc).conj (successor b.castSucc.castSucc (Fin.last m).castSucc)) :=
      of_eq (by simp only [B,Formula.raise,Formula.rename,numeral_rename,successor_rename]) (under hB C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hs := ih hZ2 w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 (.conjL hB2) (.conjL hC)
    have ho := add_succ_backward hZ2 w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc
      (Fin.last (m+1)) c.castSucc.castSucc hw2 (SyntaxNumerals.range hZ2 i _ _ hw2 ha2)
      (SyntaxNumerals.range hZ2 j _ _ hw2 (.conjL hB2)) (.conjR hB2) hs (.conjR hC)
    exact of_eq (by simp only [Formula.raise,sum_rename]) ho

end PPAC.Migration.Internal.SyntaxNumeralAddition
