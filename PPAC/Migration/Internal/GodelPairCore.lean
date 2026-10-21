import PPAC.Migration.Internal.GodelPairPolynomial

/-! 固定分支的原配数在全部内部自然输入上实际存在唯一且输出属于ω。 -/
namespace PPAC.Migration.Internal.GodelPairCore
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) : Derives Γ (existsCode w a b) := by
  apply SourcePropositional.by_cases (.mem a b) (existsCode w a b)
  · let M := Formula.mem a b
    let Γm := Context.add M Γ
    have hl := GodelPairBranchExistence.lower_exists (ZFContext.add hZ M) w a b (add hw M) (add ha M) (add hb M)
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (lower w.castSucc a.castSucc b.castSucc (Fin.last m))
    let Ξ := Context.add P (Context.image Formula.raise Γm)
    change Derives Γm (.ex P) at hl
    apply Derives.exE (p := P) hl
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hGuard : Derives Ξ (.mem a.castSucc b.castSucc) := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) P
    have hc : Derives Ξ (code w.castSucc a.castSucc b.castSucc (Fin.last m)) := .disjL (.conjI hGuard (.conjR hP))
    simpa only [Formula.raise, existsCode_rename] using intro_existsCode _ _ _ _ (.conjL hP) hc
  · let M := (Formula.mem a b).neg
    let Γm := Context.add M Γ
    have hu := GodelPairBranchExistence.upper_exists (ZFContext.add hZ M) w a b (add hw M) (add ha M) (add hb M)
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (upper w.castSucc a.castSucc b.castSucc (Fin.last m))
    let Ξ := Context.add P (Context.image Formula.raise Γm)
    change Derives Γm (.ex P) at hu
    apply Derives.exE (p := P) hu
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hGuard : Derives Ξ (Formula.mem a.castSucc b.castSucc).neg := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) P
    have hc : Derives Ξ (code w.castSucc a.castSucc b.castSucc (Fin.last m)) := .disjR (.conjI hGuard (.conjR hP))
    simpa only [Formula.raise, existsCode_rename] using intro_existsCode _ _ _ _ (.conjL hP) hc

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w a b p)) : Derives Γ (.mem p w) := by
  apply Derives.disjE hp
  · exact GodelPairPolynomial.lower_range (ZFContext.add hZ _) _ _ _ _ (add hw _) (.conjR (.hyp (Or.inl rfl)))
  · exact GodelPairPolynomial.upper_range (ZFContext.add hZ _) _ _ _ _ (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (code w a b p)) (hq : Derives Γ (code w a b q)) : Derives Γ (.equal p q) := by
  apply Derives.disjE hp
  · apply Derives.disjE (add hq _)
    · exact GodelPairPolynomial.lower_unique (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ (add (add hw _) _) (add (add ha _) _) (add (add hb _) _)
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hq _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (.conjL (.hyp (Or.inl rfl))))
    · exact GodelPairPolynomial.upper_unique (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ (add (add hw _) _) (add (add (ha) _) _) (add (add hb _) _)
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) : Derives Γ (GodelPairSyntax.fiber w a b) := by
  have hp := exists_code hZ w a b hw ha hb
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc a.castSucc b.castSucc (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hu : Derives Ξ (.all ((code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Q := code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Q
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Q
    have hOld : Derives Δ (code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, code_rename] using under (Derives.conjR hP) Q
    exact unique hZ2 _ _ _ _ _ hw2 (under (under ha P) Q) (under (under hb P) Q) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (GodelPairSyntax.fiber w.castSucc a.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hP hu
  simpa only [Formula.raise, GodelPairSyntax.fiber_rename] using hout

theorem lower_guard_iff {m} {Γ : Context m} (w a b p : Fin m) (hab : Derives Γ (.mem a b)) :
    Derives Γ ((code w a b p).iff (lower w a b p)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add (add hab _) _))
  · apply Derives.impI
    exact .disjL (.conjI (add hab _) (.hyp (Or.inl rfl)))

theorem upper_guard_iff {m} {Γ : Context m} (w a b p : Fin m) (hab : Derives Γ (Formula.mem a b).neg) :
    Derives Γ ((code w a b p).iff (upper w a b p)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (.impE (add (add hab _) _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .disjR (.conjI (add hab _) (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.GodelPairCore
