import PPAC.Migration.Internal.RawCodeProjectionSyntax

/-! 任意原始标签的head/tail投影总单值、自然范围、零码及精确原配数构造律。 -/
namespace PPAC.Migration.Internal.RawCodeProjection
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeProjectionSyntax

theorem exists_step {m} {Γ : Context m} (head : Bool) (w x : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (hasStep head w x) := by
  let P := PairingProjectionSyntax.step true false w.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PairingProjection.exists_step true false w x hw)
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  let Y := PairingProjectionSyntax.step false head w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) (PairingProjection.exists_step false head w.castSucc (Fin.last m) hw1)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (PairingProjectionSyntax.step true false w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, PairingProjectionSyntax.step_rename] using under hP Y
  have hout := intro_value head w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))
    (intro_step head _ _ _ _ hP2 (.hyp (Or.inl rfl)))
  simpa only [Formula.raise, hasStep_rename] using hout

theorem range_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step head w x y)) : Derives Γ (.mem y w) := by
  let B := body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact PairingProjection.range_point (ZFContext.under hZ B) false head _ _ _ hw1 (.conjR hB)

theorem functional_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step head w x y)) (hz : Derives Γ (step head w x z)) : Derives Γ (.equal y z) := by
  let P := body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hy
  have hz1 : Derives Ξ (step head w.castSucc x.castSucc z.castSucc) := by simpa only [Formula.raise, step_rename] using under hz P
  let Q := body head w.castSucc.castSucc x.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) hz1
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw P) Q
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (body head w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, body_rename] using under hP Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have he := PairingProjection.functional_point hZ2 true false _ _ _ _ hw2 (.conjL hP2) (.conjL hQ)
  have hy2 := PairingProjection.input_subst false head _ _ _ _ he (.conjR hP2)
  exact PairingProjection.functional_point hZ2 false head _ _ _ _ hw2 hy2 (.conjR hQ)

theorem zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) (hy : Derives Γ (step head w x y)) : Derives Γ (empty y) := by
  let B := body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hx1 : Derives Δ (empty x.castSucc) := by simpa only [Formula.raise, empty_rename] using under hx B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := PairingProjectionNatural.raw_zero false _ _ _ hx1 (.conjL hB)
  have hout := PairingProjectionNatural.bare_zero (ZFContext.under hZ B) head _ _ _ hw1 hp (.conjR hB)
  simpa only [Formula.raise, empty_rename] using hout

theorem intro_raw_pair {m} {Γ : Context m} (head : Bool) (w tag p a b x : Fin m)
    (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem p w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x)) (hc : Derives Γ (GodelPairSyntax.code w a b p)) :
    Derives Γ (step head w x (if head then a else b)) :=
  intro_step head _ _ _ p (.disjL (PairingProjection.selected_code true false _ _ _ _ ht hp hr))
    (.disjL (PairingProjection.selected_code false head _ _ _ _ ha hb hc))

theorem on_raw_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w tag p a b x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem p w))
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x)) (hc : Derives Γ (GodelPairSyntax.code w a b p))
    (hy : Derives Γ (step head w x y)) : Derives Γ (.equal y (if head then a else b)) :=
  functional_point hZ head w x y _ hw hy (intro_raw_pair head _ _ _ _ _ _ ht hp ha hb hr hc)

theorem on_raw_pair_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w tag p a b x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem p w))
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x)) (hc : Derives Γ (GodelPairSyntax.code w a b p)) :
    Derives Γ ((step head w x y).iff (.equal y (if head then a else b))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact on_raw_pair (ZFContext.add hZ _) head _ _ _ _ _ _ _ (add hw _) (add ht _) (add hp _) (add ha _) (add hb _) (add hr _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact output_subst head w x _ y (eq_symm (.hyp (Or.inl rfl))) (add (intro_raw_pair head w tag p a b x ht hp ha hb hr hc) _)

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) : Derives Γ (step head w x x) := by
  have hxw := OmegaStructureAlgebra.zero_member w x (ZFContext.arithmetic hZ).base.extensionality hw hx
  have hp : Derives Γ (PairingProjectionSyntax.step true false w x x) := .disjR (.conjI (PairingProjectionNatural.raw_zero_unselected false w x hx) hx)
  have hc : Derives Γ (PairingProjectionSyntax.step false head w x (if head then x else x)) :=
    .disjL (PairingProjection.selected_code false head w x x x hxw hxw (GodelUnpairTransitions.zero_code hZ w x hw hx))
  have hc1 : Derives Γ (PairingProjectionSyntax.step false head w x x) := by simpa only [ite_self] using hc
  exact intro_step head w x x x hp hc1

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) : Derives Γ ((step head w x y).iff (empty y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact zero (ZFContext.add hZ _) head w x y (add hw _) (add hx _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have he := OmegaUniversal.empty_unique x y (add (ZFContext.arithmetic hZ).base.extensionality _) (add hx _) (.hyp (Or.inl rfl))
    exact output_subst head w x x y he (add (zero_value hZ head w x hw hx) _)

end PPAC.Migration.Internal.RawCodeProjection
