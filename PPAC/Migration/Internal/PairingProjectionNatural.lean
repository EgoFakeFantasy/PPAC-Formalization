import PPAC.Migration.Internal.PairingProjection

/-! 原裸配数在全部内部自然码上可解，原节点正码可解且零码精确补零。 -/
namespace PPAC.Migration.Internal.PairingProjectionNatural
open Source SourceAlgebra SourceLogic OmegaSyntax PairingProjectionSyntax

theorem bare_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) : Derives Γ (hasSelected false head w x) := by
  let B := GodelUnpairSyntax.witness w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply GodelUnpairSyntax.eliminate_preimage w x _ (GodelUnpairExistence.preimage_exists hZ w x hw hx)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := intro_hasSelected false head w.castSucc.castSucc x.castSucc.castSucc _
    (PairingProjection.selected_code false head _ _ _ _ (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB))
  simpa only [Formula.raise, hasSelected_rename] using hout

theorem raw_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hp : Derives Γ (empty x).neg) : Derives Γ (hasSelected true head w x) := by
  let B := StructuralNodeDecodeSyntax.witness w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralNodeDecodeSyntax.eliminate_preimage w x _ (StructuralNodeDecodeExistence.preimage_exists hZ w x hw hx hp)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := intro_hasSelected true head w.castSucc.castSucc x.castSucc.castSucc _
    (PairingProjection.selected_code true head _ _ _ _ (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB))
  simpa only [Formula.raise, hasSelected_rename] using hout

theorem raw_selected_positive {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hy : Derives Γ (selected true head w x y)) : Derives Γ (empty x).neg := by
  let B := body true head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := StructuralNodeProperties.positive w.castSucc _ _ x.castSucc (.conjR hB)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem raw_zero_unselected {m} {Γ : Context m} (head : Bool) (w x : Fin m)
    (hx : Derives Γ (empty x)) : Derives Γ (hasSelected true head w x).neg := by
  apply Derives.impI
  let E := hasSelected true head w x
  let B := selected true head w.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
  apply Derives.exE (p := B) (.hyp (Or.inl rfl))
  have hx1 : Derives Δ (empty x.castSucc) := by simpa only [Formula.raise, empty_rename] using under (add hx E) B
  exact .impE (raw_selected_positive head _ _ _ (.hyp (Or.inl rfl))) hx1

theorem raw_zero {m} {Γ : Context m} (head : Bool) (w x y : Fin m)
    (hx : Derives Γ (empty x)) (hy : Derives Γ (step true head w x y)) : Derives Γ (empty y) :=
  PairingProjection.off_selected true head w x y (raw_zero_unselected head w x hx) hy

theorem natural_raw_unselected_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hu : Derives Γ (hasSelected true head w x).neg) :
    Derives Γ (empty x) := by
  apply SourcePropositional.by_cases (empty x) (empty x)
  · exact .hyp (Or.inl rfl)
  · exact .botE (.impE (add hu _) (raw_selected (ZFContext.add hZ _) head w x (add hw _) (add hx _) (.hyp (Or.inl rfl))))

theorem bare_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) (hy : Derives Γ (step false head w x y)) : Derives Γ (empty y) := by
  have hxw := OmegaStructureAlgebra.zero_member w x (ZFContext.arithmetic hZ).base.extensionality hw hx
  have he := PairingProjection.on_code hZ false head w x x x y hw hxw hxw (GodelUnpairTransitions.zero_code hZ w x hw hx) hy
  have he1 : Derives Γ (.equal y x) := by simpa only [ite_self] using he
  exact NaturalMultiplicationLaws.empty_subst x y (eq_symm he1) hx

end PPAC.Migration.Internal.PairingProjectionNatural
