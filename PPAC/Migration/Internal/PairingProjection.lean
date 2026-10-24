import PPAC.Migration.Internal.PairingProjectionSyntax

/-! 全内部集合上的原裸配数／后继节点的总单值分量投影；所有实际选择与补零均在对象公式中。 -/
namespace PPAC.Migration.Internal.PairingProjection
open Source SourceAlgebra SourceLogic OmegaSyntax PairingProjectionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem body_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y a z b : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (body raw head w x y a)) (hz : Derives Γ (body raw head w x z b)) : Derives Γ (.equal y z) := by
  cases raw <;> cases head
  · exact .conjR (GodelPairInjective.injective hZ w a y b z x hw (.conjR (.conjL hy)) (.conjL (.conjL hy)) (.conjR (.conjL hz)) (.conjL (.conjL hz)) (.conjR hy) (.conjR hz))
  · exact .conjL (GodelPairInjective.injective hZ w y a z b x hw (.conjL (.conjL hy)) (.conjR (.conjL hy)) (.conjL (.conjL hz)) (.conjR (.conjL hz)) (.conjR hy) (.conjR hz))
  · exact .conjR (StructuralNodeCore.injective hZ w a y b z x hw (.conjR (.conjL hy)) (.conjL (.conjL hy)) (.conjR (.conjL hz)) (.conjL (.conjL hz)) (.conjR hy) (.conjR hz))
  · exact .conjL (StructuralNodeCore.injective hZ w y a z b x hw (.conjL (.conjL hy)) (.conjR (.conjL hy)) (.conjL (.conjL hz)) (.conjR (.conjL hz)) (.conjR hy) (.conjR hz))

theorem selected_range {m} {Γ : Context m} (raw head : Bool) (w x y : Fin m)
    (hy : Derives Γ (selected raw head w x y)) : Derives Γ (.mem y w) := by
  let B := body raw head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hy
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjL (.conjL hB)

theorem selected_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (selected raw head w x y)) (hz : Derives Γ (selected raw head w x z)) : Derives Γ (.equal y z) := by
  let A := body raw head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hy
  apply Derives.exE (p := A) hy
  have hz1 : Derives Ξ (selected raw head w.castSucc x.castSucc z.castSucc) := by simpa only [Formula.raise, selected_rename] using under hz A
  let B := body raw head w.castSucc.castSucc x.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex B) at hz1
  apply Derives.exE (p := B) hz1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ A) B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw A) B
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA2 : Derives Δ (body raw head w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [A, Formula.raise, body_rename] using under hA B
  exact body_unique hZ2 raw head _ _ _ _ _ _ hw2 hA2 (.hyp (Or.inl rfl))

theorem exists_step {m} {Γ : Context m} (raw head : Bool) (w x : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (hasStep raw head w x) := by
  apply SourcePropositional.by_cases (hasSelected raw head w x) (hasStep raw head w x)
  · let C := hasSelected raw head w x
    let Γc := Context.add C Γ
    let Y := selected raw head w.castSucc x.castSucc (Fin.last m)
    let Δ := Context.add Y (Context.image Formula.raise Γc)
    have hy : Derives Γc (.ex Y) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Y) hy
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have hout := intro_value raw head w.castSucc x.castSucc (Fin.last m) (Derives.disjL (q := (hasSelected raw head w.castSucc x.castSucc).neg.conj (empty (Fin.last m))) hY)
    simpa only [Formula.raise, hasStep_rename] using hout
  · let C := (hasSelected raw head w x).neg
    let Γc := Context.add C Γ
    have hz : Derives Γc (zeroIn w) := add (.conjL (.conjL hw)) C
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Δ := Context.add Z (Context.image Formula.raise Γc)
    change Derives Γc (.ex Z) at hz
    apply Derives.exE (p := Z) hz
    have hC : Derives Δ (hasSelected raw head w.castSucc x.castSucc).neg := by
      simpa only [C, Formula.raise, Formula.neg, Formula.rename, hasSelected_rename] using under (Derives.hyp (Γ := Γc) (Or.inl rfl)) Z
    have hZ : Derives Δ Z := .hyp (Or.inl rfl)
    have hst : Derives Δ (step raw head w.castSucc x.castSucc (Fin.last m)) := .disjR (.conjI hC (.conjR hZ))
    simpa only [Formula.raise, hasStep_rename] using intro_value raw head w.castSucc x.castSucc (Fin.last m) hst

theorem functional_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step raw head w x y)) (hz : Derives Γ (step raw head w x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact selected_unique (ZFContext.add (ZFContext.add hZ _) _) raw head w x y z (add (add hw _) _)
        (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (intro_hasSelected raw head w x y (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (intro_hasSelected raw head w x z (.hyp (Or.inl rfl))))
    · exact OmegaUniversal.empty_unique y z (ZFContext.arithmetic (ZFContext.add (ZFContext.add hZ _) _)).base.extensionality
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem range_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step raw head w x y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hy
  · exact selected_range raw head w x y (.hyp (Or.inl rfl))
  · exact OmegaStructureAlgebra.zero_member w y (add (ZFContext.arithmetic hZ).base.extensionality _) (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem selected_code {m} {Γ : Context m} (raw head : Bool) (w a b x : Fin m)
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hc : Derives Γ (encoded raw w a b x)) :
    Derives Γ (selected raw head w x (if head then a else b)) := by
  cases head
  · exact intro_selected raw false w x b a (.conjI (.conjI hb ha) hc)
  · exact intro_selected raw true w x a b (.conjI (.conjI ha hb) hc)

theorem on_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w a b x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (encoded raw w a b x)) (hy : Derives Γ (step raw head w x y)) :
    Derives Γ (.equal y (if head then a else b)) :=
  functional_point hZ raw head w x y _ hw hy (.disjL (selected_code raw head w a b x ha hb hc))

theorem off_selected {m} {Γ : Context m} (raw head : Bool) (w x y : Fin m)
    (hn : Derives Γ (hasSelected raw head w x).neg) (hy : Derives Γ (step raw head w x y)) : Derives Γ (empty y) := by
  apply Derives.disjE hy
  · exact .botE (.impE (add hn _) (intro_hasSelected raw head w x y (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

theorem input_subst {m} {Γ : Context m} (raw head : Bool) (w x z y : Fin m)
    (he : Derives Γ (.equal x z)) (hy : Derives Γ (step raw head w x y)) : Derives Γ (step raw head w z y) := by
  let P := step raw head w.castSucc (Fin.last m) y.castSucc
  have h0 : P.instantiate x = step raw head w x y := by simp only [P, Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = step raw head w z y := by simp only [P, Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hi : Derives Γ (P.instantiate x) := h0.symm ▸ hy
  exact h1 ▸ Derives.eqSubst P he hi

end PPAC.Migration.Internal.PairingProjection
