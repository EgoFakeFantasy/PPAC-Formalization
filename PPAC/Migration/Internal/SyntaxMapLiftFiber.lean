import PPAC.Migration.Internal.SyntaxMapLift

/-! 提升自然码的全候选唯一性与实际纤维；输入/输出均为真实MapCode。 -/
namespace PPAC.Migration.Internal.SyntaxMapLiftFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapCodeSyntax SyntaxIndexLiftSyntax SyntaxMapLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_code {m} {Γ : Context m} (w a c k u v l : Fin m)
    (hl : Derives Γ (codedLift w a c k u v l)) : Derives Γ (mapCode w a c k) := by
  let B := body w a c k u v l
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_lift w a c k u v l _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code _ _ _ _ _ (.conjL hB)
  simpa only [Formula.raise, mapCode_rename] using ho

theorem output_code {m} {Γ : Context m} (w a c k u v l : Fin m)
    (hl : Derives Γ (codedLift w a c k u v l)) : Derives Γ (mapCode w u v l) := by
  let B := body w a c k u v l
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_lift w a c k u v l _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code _ _ _ _ _ (.conjR (.conjR hB))
  simpa only [Formula.raise, mapCode_rename] using ho

theorem output_natural {m} {Γ : Context m} (w a c k u v l : Fin m)
    (hl : Derives Γ (codedLift w a c k u v l)) : Derives Γ (.mem l w) :=
  SyntaxMapCodeDecode.natural w u v l (output_code w a c k u v l hl)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k u v l q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (codedLift w a c k u v l)) (hq : Derives Γ (codedLift w a c k u v q)) :
    Derives Γ (.equal l q) := by
  have hk := input_code w a c k u v l hl
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hk
  apply Derives.exE hk
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hl1 : Derives Δ (codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc l.castSucc) := by
    simpa only [Formula.raise, codedLift_rename] using under hl R
  have hq1 : Derives Δ (codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc q.castSucc) := by
    simpa only [Formula.raise, codedLift_rename] using under hq R
  exact SyntaxMapLift.unique_at_source (ZFContext.under hZ R) _ _ _ _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hl1 hq1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k u v : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (mapCode w a c k))
    (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v c)) :
    Derives Γ (SyntaxMapLiftSyntax.fiber w a c k u v) := by
  have he := SyntaxMapLift.exists_code hZ w a c k u v hw hk hu hv
  let L := codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc (Fin.last m)
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at he
  apply Derives.exE he
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have huq : Derives Ξ (.all
      ((codedLift w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc
        u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).imp
          (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Q := codedLift w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Q
    have hl2 : Derives Δ (codedLift w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc
        u.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [L, Formula.raise, codedLift_rename] using under hL Q
    exact unique (ZFContext.under (ZFContext.under hZ L) Q) _ _ _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hl2
  have ho : Derives Ξ (SyntaxMapLiftSyntax.fiber w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, codedLift_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hL huq
  simpa only [Formula.raise, SyntaxMapLiftSyntax.fiber_rename] using ho
end PPAC.Migration.Internal.SyntaxMapLiftFiber
