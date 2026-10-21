import PPAC.Migration.Internal.SyntaxForestInjective

/-! 不同有限字段数的原森林互斥；由真实内部数码长度与原长度唯一性排除额外字段。 -/
namespace PPAC.Migration.Internal.SyntaxForestArity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax SyntaxForestSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (hkl : k ≠ l) (w : Fin m)
    (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (forest k w xs n)) (hy : Derives Γ (forest l w ys n)) : Derives Γ .bot := by
  have hu := SyntaxNumerals.exists_numeral hZ k w hw
  let U := (Formula.mem (Fin.last m) w.castSucc).conj (numeral k (Fin.last m))
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ U
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw U
  have hv := SyntaxNumerals.exists_numeral hZ1 l w.castSucc hw1
  let V := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (numeral l (Fin.last (m+1)))
  let Δ := Context.add V (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 V
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 V
  have hx2 : Derives Δ (forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [Formula.raise, forest_rename] using under (under hx U) V
  have hy2 : Derives Δ (forest l w.castSucc.castSucc (fun i => (ys i).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [Formula.raise, forest_rename] using under (under hy U) V
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hu2 : Derives Δ (numeral k (Fin.last m).castSucc) := by simpa only [Formula.raise, numeral_rename] using under (Derives.conjR hU) V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hlenK := SyntaxForestLength.at_numeral hZ2 k _ _ _ _ hw2 hx2 hu2
  have hlenL := SyntaxForestLength.at_numeral hZ2 l _ _ _ _ hw2 hy2 (.conjR hV)
  have heq := StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 hlenK hlenL
  exact .impE (SyntaxNumerals.different hZ2 k l hkl _ _ hu2 (.conjR hV)) heq
end PPAC.Migration.Internal.SyntaxForestArity
