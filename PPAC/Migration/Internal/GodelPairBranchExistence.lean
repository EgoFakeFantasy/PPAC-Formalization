import PPAC.Migration.Internal.GodelPairSyntax

/-! 两个分支实际构造自然平方及逐次自然和；不固定宿主配数函数。 -/
namespace PPAC.Migration.Internal.GodelPairBranchExistence
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax
open NaturalAdditionSyntax (sum sum_rename existsSum existsSum_rename)
open NaturalMultiplicationSyntax (product product_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) : Derives Γ (existsLower w a b) := by
  have hq := mul_exists hZ w b b hw hb hb
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc b.castSucc b.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hp := add_exists hZ1 w.castSucc (Fin.last m) a.castSucc hw1 (.conjL hQ) (under ha Q)
  let P := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add P (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hQ2 : Derives Δ Q.raise := under hQ P
  have hSquare : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Q, Formula.raise, Formula.rename, product_rename] using Derives.conjR hQ2
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hl := intro_lower _ _ _ _ _ hSquare (.conjR hP)
  have hout := intro_existsLower _ _ _ _ (.conjL hP) hl
  simpa only [Formula.raise, existsLower_rename] using hout

theorem upper_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) : Derives Γ (existsUpper w a b) := by
  have hq := mul_exists hZ w a a hw ha ha
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc a.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have ht := add_exists hZ1 w.castSucc (Fin.last m) a.castSucc hw1 (.conjL hQ) (under ha Q)
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1)))
  let Ψ := Context.add T (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ2 : ZFContext.Evidence Ψ := ZFContext.under hZ1 T
  have hw2 : Derives Ψ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 T
  have hT : Derives Ψ T := .hyp (Or.inl rfl)
  have hp := add_exists hZ2 w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc hw2 (.conjL hT) (under (under hb Q) T)
  let P := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (sum w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc b.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ := Context.add P (Context.image Formula.raise Ψ)
  change Derives Ψ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hQ3 : Derives Δ Q.raise.raise := under (under hQ T) P
  have hT3 : Derives Δ T.raise := under hT P
  have hSquare : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [Q, Formula.raise, Formula.rename, product_rename] using Derives.conjR hQ3
  have hSum : Derives Δ (sum w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := by
    simpa only [T, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hT3
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hu := intro_upper _ _ _ _ _ _ hSquare hSum (.conjR hP)
  have hout := intro_existsUpper _ _ _ _ (.conjL hP) hu
  simpa only [Formula.raise, existsUpper_rename] using hout
end PPAC.Migration.Internal.GodelPairBranchExistence
