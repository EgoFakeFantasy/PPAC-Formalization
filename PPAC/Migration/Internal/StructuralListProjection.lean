import PPAC.Migration.Internal.StructuralListProjectionSyntax

/-! 全内部集合上的原Cons head/tail投影：实际存在、单值、自然范围及原构造器求值。 -/
namespace PPAC.Migration.Internal.StructuralListProjection
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem body_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y a z b : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (body head w x y a)) (hz : Derives Γ (body head w x z b)) : Derives Γ (.equal y z) := by
  cases head
  · exact .conjR (StructuralConsUnique.injective hZ w a y b z x hw (.conjR (.conjL hy)) (.conjL (.conjL hy))
      (.conjR (.conjL hz)) (.conjL (.conjL hz)) (.conjR hy) (.conjR hz))
  · exact .conjL (StructuralConsUnique.injective hZ w y a z b x hw (.conjL (.conjL hy)) (.conjR (.conjL hy))
      (.conjL (.conjL hz)) (.conjR (.conjL hz)) (.conjR hy) (.conjR hz))

theorem selected_range {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hy : Derives Γ (selected head w x y)) : Derives Γ (.mem y w) := by
  let B := body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hy
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjL (.conjL hB)

theorem selected_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (selected head w x y)) (hz : Derives Γ (selected head w x z)) : Derives Γ (.equal y z) := by
  let A := body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hy
  apply Derives.exE (p := A) hy
  have hz1 : Derives Ξ (selected head w.castSucc x.castSucc z.castSucc) := by simpa only [Formula.raise, selected_rename] using under hz A
  let B := body head w.castSucc.castSucc x.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex B) at hz1
  apply Derives.exE (p := B) hz1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ A) B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw A) B
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hA2 : Derives Δ (body head w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [A, Formula.raise, body_rename] using under hA B
  exact body_unique hZ2 head _ _ _ _ _ _ hw2 hA2 (.hyp (Or.inl rfl))

theorem exists_step {m} {Γ : Context m} (head : Bool) (w x : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (hasStep head w x) := by
  apply SourcePropositional.by_cases (hasCons head w x) (hasStep head w x)
  · let C := hasCons head w x
    let Γc := Context.add C Γ
    let Y := selected head w.castSucc x.castSucc (Fin.last m)
    let Δ := Context.add Y (Context.image Formula.raise Γc)
    have hy : Derives Γc (.ex Y) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Y) hy
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have hout := intro_value head w.castSucc x.castSucc (Fin.last m) (Derives.disjL (q := (hasCons head w.castSucc x.castSucc).neg.conj (empty (Fin.last m))) hY)
    simpa only [Formula.raise, hasStep_rename] using hout
  · let C := (hasCons head w x).neg
    let Γc := Context.add C Γ
    have hz : Derives Γc (zeroIn w) := add (.conjL (.conjL hw)) C
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Δ := Context.add Z (Context.image Formula.raise Γc)
    change Derives Γc (.ex Z) at hz
    apply Derives.exE (p := Z) hz
    have hC : Derives Δ (hasCons head w.castSucc x.castSucc).neg := by
      simpa only [C, Formula.raise, Formula.neg, Formula.rename, hasCons_rename] using under (Derives.hyp (Γ := Γc) (Or.inl rfl)) Z
    have hZ : Derives Δ Z := .hyp (Or.inl rfl)
    have hst : Derives Δ (step head w.castSucc x.castSucc (Fin.last m)) := .disjR (.conjI hC (.conjR hZ))
    simpa only [Formula.raise, hasStep_rename] using intro_value head w.castSucc x.castSucc (Fin.last m) hst

theorem functional_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step head w x y)) (hz : Derives Γ (step head w x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact selected_unique (ZFContext.add (ZFContext.add hZ _) _) head w x y z (add (add hw _) _)
        (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (intro_hasCons head w x y (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (intro_hasCons head w x z (.hyp (Or.inl rfl))))
    · exact OmegaUniversal.empty_unique y z (ZFContext.arithmetic (ZFContext.add (ZFContext.add hZ _) _)).base.extensionality
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem range_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step head w x y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hy
  · exact selected_range head w x y (.hyp (Or.inl rfl))
  · exact OmegaStructureAlgebra.zero_member w y (add (ZFContext.arithmetic hZ).base.extensionality _) (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem selected_cons {m} {Γ : Context m} (head : Bool) (w h t n : Fin m)
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n)) :
    Derives Γ (selected head w n (if head then h else t)) := by
  cases head
  · exact intro_selected false w n t h (.conjI (.conjI ht hh) hc)
  · exact intro_selected true w n h t (.conjI (.conjI hh ht) hc)

theorem on_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w h t n y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hy : Derives Γ (step head w n y)) : Derives Γ (.equal y (if head then h else t)) :=
  functional_point hZ head w n y _ hw hy (.disjL (selected_cons head w h t n hh ht hc))

theorem selected_nil_absurd {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hy : Derives Γ (selected head w n y)) : Derives Γ .bot := by
  let B := body head w.castSucc n.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hy
  apply Derives.exE (p := B) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under hn B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact StructuralConsUnique.disjoint hZ1 _ _ _ _ hw1 hn1 (.conjR hB)

theorem nil_no_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) : Derives Γ (hasCons head w n).neg := by
  apply Derives.impI
  let C := hasCons head w n
  let Γc := Context.add C Γ
  let Y := selected head w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γc)
  have hy : Derives Γc (.ex Y) := .hyp (Or.inl rfl)
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ C) Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw C) Y
  have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under (add hn C) Y
  exact selected_nil_absurd hZ1 head _ _ _ hw1 hn1 (.hyp (Or.inl rfl))

theorem off_cons {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hn : Derives Γ (hasCons head w x).neg) (hy : Derives Γ (step head w x y)) : Derives Γ (empty y) := by
  apply Derives.disjE hy
  · exact .botE (.impE (add hn _) (intro_hasCons head w x y (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

theorem on_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hy : Derives Γ (step head w n y)) : Derives Γ (empty y) :=
  off_cons head w n y (nil_no_cons hZ head w n hw hn) hy
end PPAC.Migration.Internal.StructuralListProjection
