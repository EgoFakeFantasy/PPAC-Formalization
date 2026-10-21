import PPAC.Migration.Internal.NaturalAdditionMonotone

/-! 非零乘积与零因子刻画，实际读取非零乘数的内部前驱及旧积。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationPositive
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nonzero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (ha0 : Derives Γ (empty a).neg) (hn0 : Derives Γ (empty n).neg) (hp : Derives Γ (product w a n p)) :
    Derives Γ (empty p).neg := by
  apply Derives.impI
  let M := empty p
  let Γm := Context.add M Γ
  have hd := OmegaStructureAlgebra.decomposition_at w n
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hn
  have ht := OmegaStructureAlgebra.nonzero_predecessor w n hd hn0
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (successor n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γm)
  have ht' : Derives Γm (.ex T) := add ht M
  apply Derives.exE (p := T) ht'
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under (ZFContext.add hZ M) T
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw M) T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hq := mul_exists hZ1 w.castSucc a.castSucc (Fin.last m) hw1 (under (add ha M) T) (.conjL hT)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (product w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Q
  have ha2 : Derives Δ (.mem a.castSucc.castSucc w.castSucc.castSucc) := under (under (add ha M) T) Q
  have ha02 : Derives Δ (empty a.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using under (under (add ha0 M) T) Q
  have hp2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc p.castSucc.castSucc) := by
    simpa only [Formula.raise, product_rename] using under (under (add hp M) T) Q
  have hT2 : Derives Δ T.raise := under hT Q
  have hs : Derives Δ (successor n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [T, Formula.raise, Formula.rename, successor_rename] using Derives.conjR hT2
  have htW : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := .conjL hT2
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hsum := mul_succ_forward hZ2 _ _ _ _ _ _ hw2 ha2 htW hs (.conjR hQ) hp2
  have hmem := NaturalDifferencePositive.sum_positive hZ2 _ _ _ _ hw2 (.conjL hQ) ha2 hsum ha02
  have hp0 : Derives Δ (empty p.castSucc.castSucc) := by
    simpa only [M, Formula.raise, empty_rename] using under (under (Derives.hyp (Γ := Γm) (Or.inl rfl)) T) Q
  exact .impE (empty_at p.castSucc.castSucc (Fin.last (m+1)) hp0) hmem

theorem zero_left_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (ha0 : Derives Γ (empty a)) (hp : Derives Γ (product w a n p)) : Derives Γ (empty p) := by
  have hall := NaturalMultiplicationZero.all_left_zero (ZFContext.arithmetic hZ) w a (ZFContext.recAdd hZ) (ZFContext.recMul hZ)
    (ZFContext.separation hZ NaturalMultiplicationZero.matrix) hw ha0
  have hi : Derives Γ ((Formula.mem n w).imp (product w a n a)) := by
    simpa only [Formula.instantiate, Formula.rename, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n hall
  have heq := mul_unique hZ w a n p a hw ha hn hp (.impE hi hn)
  exact NaturalMultiplicationLaws.empty_subst a p (eq_symm heq) ha0

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hp : Derives Γ (product w a n p)) :
    Derives Γ ((empty p).iff ((empty a).disj (empty n))) := by
  apply Derives.conjI
  · apply Derives.impI
    apply SourcePropositional.by_cases (empty a) ((empty a).disj (empty n))
    · exact .disjL (.hyp (Or.inl rfl))
    · apply Derives.disjR
      apply Derives.classical
      let Δ := Context.add (empty n).neg (Context.add (empty a).neg (Context.add (empty p) Γ))
      have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _
      have hbad := nonzero hZ3 w a n p (add (add (add hw _) _) _) (add (add (add ha _) _) _) (add (add (add hn _) _) _)
        (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)) (add (add (add hp _) _) _)
      exact .impE hbad (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact zero_left_output (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ (add (add hw _) _) (add (add ha _) _) (add (add hn _) _) (.hyp (Or.inl rfl)) (add (add hp _) _)
    · exact NaturalMultiplicationLaws.zero_forward w a n p (.hyp (Or.inl rfl)) (add (add hp _) _)
end PPAC.Migration.Internal.NaturalMultiplicationPositive
