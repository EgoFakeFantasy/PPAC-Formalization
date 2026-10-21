import PPAC.Migration.Internal.GodelPairBands

/-! 相同编码值的平方区间具有唯一自然指标，覆盖全部内部ω。 -/
namespace PPAC.Migration.Internal.GodelPairBandUnique
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairBandSyntax GodelPairArithmetic
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem not_lt {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hp : Derives Γ (.mem p w))
    (hA : Derives Γ (band w a p)) (hB : Derives Γ (band w b p)) (hab : Derives Γ (.mem a b)) : Derives Γ .bot := by
  have hs := Derives.impE (step_at w a (.conjL hw)) ha
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) a.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ S
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hv := mul_exists hZ1 w.castSucc (Fin.last m) (Fin.last m) hw1 (.conjL hS) (.conjL hS)
  let V := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (product w.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ψ := Context.add V (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hZ2 : ZFContext.Evidence Ψ := ZFContext.under hZ1 V
  have hw2 : Derives Ψ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 V
  have hq := mul_exists hZ2 w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc hw2 (under (under hb S) V) (under (under hb S) V)
  let Q := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (product w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ := Context.add Q (Context.image Formula.raise Ψ)
  change Derives Ψ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ3 : ZFContext.Evidence Δ := ZFContext.under hZ2 Q
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise := under (under (under h S) V) Q
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hS3 : Derives Δ ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc)) := by
    simpa only [S, Formula.raise, Formula.rename, successor_rename] using under (under hS V) Q
  have hV : Derives Ψ V := .hyp (Or.inl rfl)
  have hV3 : Derives Δ ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj
      (product w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)) := by
    simpa only [V, Formula.raise, Formula.rename, product_rename] using under hV Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hA3 : Derives Δ (band w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, band_rename] using lift hA
  have hB3 : Derives Δ (band w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, band_rename] using lift hB
  have hsb := successor_below hZ3 _ _ _ _ hw3 (lift ha) (lift hb) (.conjR hS3) (lift hab)
  have hvq := square_monotone hZ3 _ _ _ _ _ hw3 (.conjL hS3) (lift hb) (.conjR hV3) (.conjR hQ) hsb
  have hqp := floor_at _ _ _ _ hB3 (.conjR hQ)
  have hvp := NaturalOrderBasic.transitive hZ3 _ _ _ _ hw3 (lift hp) hvq hqp
  have hpv := ceiling_at _ _ _ _ _ hA3 (.conjR hS3) (.conjR hV3)
  exact NaturalOrderBasic.below_not_reverse hZ3 _ _ _ hw3 (.conjL hV3) hvp hpv

theorem index_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hp : Derives Γ (.mem p w))
    (hA : Derives Γ (band w a p)) (hB : Derives Γ (band w b p)) : Derives Γ (.equal a b) := by
  apply Derives.disjE (NaturalOrderBasic.compare hZ w a b hw ha hb)
  · exact .hyp (Or.inl rfl)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (not_lt (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ (add (add hw _) _) (add (add ha _) _) (add (add hb _) _) (add (add hp _) _)
        (add (add hA _) _) (add (add hB _) _) (.hyp (Or.inl rfl)))
    · exact .botE (not_lt (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ (add (add hw _) _) (add (add hb _) _) (add (add ha _) _) (add (add hp _) _)
        (add (add hB _) _) (add (add hA _) _) (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.GodelPairBandUnique
