import PPAC.Migration.Internal.FixedAxiomPacketFacts

/-! 固定小叶包的实际内部码存在；基数、乘积、和及根码见证全部对象EX构造／消去。 -/
namespace PPAC.Migration.Internal.FixedAxiomPacketExistence
open Source SourceAlgebra SourceLogic OmegaSyntax FixedAxiomPacketSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix NaturalMultiplicationSyntax.product NaturalAdditionSyntax.sum SyntaxNumeralSyntax.numeral

theorem exists_packet {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsLeaf tag w) := by
  let B0 := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 256 (Fin.last m))
  let Γ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have h0 : Derives Γ1 B0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B0)
  let B1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last (m+1)))
  let Γ2 := Context.add B1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := B1) (SyntaxNumerals.exists_numeral hZ1 tag w.castSucc hw1)
  have h1 : Derives Γ2 B1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 B1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B1)
  have hn0_2 : Derives Γ2 (.mem (Fin.last m).castSucc w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (Derives.conjL h0) B1)
  let B2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)))
  let Γ3 := Context.add B2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := B2) (ZFArithmetic.mul_exists hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc hw2 hn0_2 hn0_2)
  have h2 : Derives Γ3 B2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 B2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B2)
  have hn0_3 : Derives Γ3 (.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under (Derives.conjL h0) B1) B2)
  have hn2_3 : Derives Γ3 (.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc) := of_eq (by rfl) (Derives.conjL h2)
  let B3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)))
  let Γ4 := Context.add B3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := B3) (ZFArithmetic.mul_exists hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) hw3 hn0_3 hn2_3)
  have h3 : Derives Γ4 B3 := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 B3
  have hw4 := of_eq (omega_rename w.castSucc.castSucc.castSucc Fin.castSucc) (under hw3 B3)
  have hn0_4 : Derives Γ4 (.mem (Fin.last m).castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under (under (Derives.conjL h0) B1) B2) B3)
  have hn1_4 : Derives Γ4 (.mem (Fin.last (m+1)).castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under (Derives.conjL h1) B2) B3)
  let B4 := (Formula.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc).conj (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+4)))
  let Γ5 := Context.add B4 (Context.image Formula.raise Γ4)
  apply Derives.exE (p := B4) (ZFArithmetic.mul_exists hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc hw4 hn0_4 hn1_4)
  have h4 : Derives Γ5 B4 := .hyp (Or.inl rfl)
  have hZ5 := ZFContext.under hZ4 B4
  have hw5 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw4 B4)
  have hn3_5 : Derives Γ5 (.mem (Fin.last (m+3)).castSucc w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (Derives.conjL h3) B4)
  have hn4_5 : Derives Γ5 (.mem (Fin.last (m+4)) w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by rfl) (Derives.conjL h4)
  let B5 := (Formula.mem (Fin.last (m+5)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)))
  let Γ6 := Context.add B5 (Context.image Formula.raise Γ5)
  apply Derives.exE (p := B5) (ZFArithmetic.add_exists hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) hw5 hn3_5 hn4_5)
  have h5 : Derives Γ6 B5 := .hyp (Or.inl rfl)
  have hw6 := of_eq (omega_rename w.castSucc.castSucc.castSucc.castSucc.castSucc Fin.castSucc) (under hw5 B5)
  have hn5_6 : Derives Γ6 (.mem (Fin.last (m+5)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by rfl) (Derives.conjL h5)
  let B6 := (Formula.mem (Fin.last (m+6)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+6)) (Fin.last (m+5)).castSucc)
  let Γ7 := Context.add B6 (Context.image Formula.raise Γ6)
  apply Derives.exE (p := B6) (Derives.impE (step_at w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)) (.conjL hw6)) hn5_6)
  have h6 : Derives Γ7 B6 := .hyp (Or.inl rfl)
  have hp0 : Derives Γ7 (SyntaxNumeralSyntax.numeral 256 (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under (under (under (under (under (Derives.conjR h0) B1) B2) B3) B4) B5) B6)
  have hp1 : Derives Γ7 (SyntaxNumeralSyntax.numeral tag (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under (under (under (under (Derives.conjR h1) B2) B3) B4) B5) B6)
  have hp2 : Derives Γ7 (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, NaturalMultiplicationSyntax.product_rename]) (under (under (under (under (Derives.conjR h2) B3) B4) B5) B6)
  have hp3 : Derives Γ7 (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, NaturalMultiplicationSyntax.product_rename]) (under (under (under (Derives.conjR h3) B4) B5) B6)
  have hp4 : Derives Γ7 (NaturalMultiplicationSyntax.product w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, NaturalMultiplicationSyntax.product_rename]) (under (under (Derives.conjR h4) B5) B6)
  have hp5 : Derives Γ7 (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc) := of_eq (by simp only [Formula.raise, NaturalAdditionSyntax.sum_rename]) (under (Derives.conjR h5) B6)
  have hn6_7 : Derives Γ7 (.mem (Fin.last (m+6)) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by rfl) (Derives.conjL h6)
  have hp6 : Derives Γ7 (successor (Fin.last (m+6)) (Fin.last (m+5)).castSucc) := of_eq (by rfl) (Derives.conjR h6)
  let env : Fin 6 → Fin (m+7) := Fin.cases (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+4)).castSucc.castSucc (Fin.cases (Fin.last (m+5)).castSucc (Fin.elim0))))))
  have hl := intro_leaf tag w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) env (.conjI hp0 (.conjI hp1 (.conjI hp2 (.conjI hp3 (.conjI hp4 (.conjI hp5 (hp6)))))))
  have ho := intro_exists tag w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) hn6_7 hl
  exact of_eq (by simp only [Formula.raise, existsLeaf_rename]) ho

end PPAC.Migration.Internal.FixedAxiomPacketExistence
