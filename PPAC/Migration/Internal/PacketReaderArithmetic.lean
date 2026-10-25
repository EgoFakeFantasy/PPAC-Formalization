import PPAC.Migration.Internal.PacketReaderGuards

/-! Unbounded value + digit * scale. Unlike the Packet bounded affine cell, no digit < scale or positivity premise is inserted. -/
namespace PPAC.Migration.Internal.PacketReaderArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic PacketAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem equation_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b v s y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (.mem v w)) (hy : Derives Γ (equation w b v s y)) : Derives Γ (.mem y w) := by
  let P := equationBody w b v s y
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hy
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact add_range (ZFContext.under hZ P) _ _ _ _ (of_eq (omega_rename w Fin.castSucc) (under hw P)) (under hv P) (.conjR hP)

theorem exists_equation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b v s : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w)) :
    Derives Γ (.ex ((Formula.mem (Fin.last m) w.castSucc).conj (equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m)))) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (NaturalMultiplicationSyntax.product w.castSucc b.castSucc s.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (mul_exists hZ w b s hw hb hs)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add N (Context.image Formula.raise Δ)
  apply Derives.exE (p := N) (add_exists hZ1 _ _ _ hw1 (under hv P) (.conjL hP))
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hp2 := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc b.castSucc s.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hP) N)
  have hEq := intro_equation w.castSucc.castSucc b.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hp2 (.conjR hN)
  have hout : Derives Ξ (.ex ((Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
      (equation w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last (m+2))))) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,equation_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hN) hEq)
  simpa only [Formula.raise,Formula.rename,equation_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc] using hout

theorem equation_digit {m} {Γ : Context m} (w b v s y d : Fin m) (he : Derives Γ (.equal b d))
    (hy : Derives Γ (equation w b v s y)) : Derives Γ (equation w d v s y) := by
  let P := equation w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc
  have h0 : P.instantiate b = equation w b v s y := by simp only [P,Formula.instantiate,equation_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate d = equation w d v s y := by simp only [P,Formula.instantiate,equation_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

end PPAC.Migration.Internal.PacketReaderArithmetic
