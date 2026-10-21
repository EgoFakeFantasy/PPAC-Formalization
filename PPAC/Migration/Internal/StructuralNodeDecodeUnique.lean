import PPAC.Migration.Internal.StructuralNodeDecodeExistence

/-! 原节点输入单射性给出精确双向解码纤维，并证明两个分量严格小于节点码。 -/
namespace PPAC.Migration.Internal.StructuralNodeDecodeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeDecodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem left_subst {m} {Γ : Context m} (w p a c b : Fin m) (he : Derives Γ (.equal a c))
    (hp : Derives Γ (witness w p a b)) : Derives Γ (witness w p c b) := by
  have hi : Derives Γ ((witness w.castSucc p.castSucc (Fin.last m) b.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst (witness w.castSucc p.castSucc (Fin.last m) b.castSucc) he hi
  simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem right_subst {m} {Γ : Context m} (w p a b d : Fin m) (he : Derives Γ (.equal b d))
    (hp : Derives Γ (witness w p a b)) : Derives Γ (witness w p a d) := by
  have hi : Derives Γ ((witness w.castSucc p.castSucc a.castSucc (Fin.last m)).instantiate b) := by
    simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst (witness w.castSucc p.castSucc a.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem exact_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p a b : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (witness w p a b)) : Derives Γ (exactAt w p a b) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.conjI
  · apply Derives.impI
    let W := witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ W
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw W
    have hp2 : Derives Δ (witness w.castSucc.castSucc p.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := by
      simpa only [Formula.raise, witness_rename] using OrderedPairElimination.under_two hp W
    have hW : Derives Δ W := .hyp (Or.inl rfl)
    exact StructuralNodeCore.injective hZ2 _ _ _ _ _ _ hw2 (.conjL (.conjL hW)) (.conjR (.conjL hW))
      (.conjL (.conjL hp2)) (.conjR (.conjL hp2)) (.conjR hW) (.conjR hp2)
  · apply Derives.impI
    let E := (Formula.equal (Fin.last m).castSucc a.castSucc.castSucc).conj (.equal (Fin.last (m+1)) b.castSucc.castSucc)
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hp2 : Derives Δ (witness w.castSucc.castSucc p.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := by
      simpa only [Formula.raise, witness_rename] using OrderedPairElimination.under_two hp E
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    exact right_subst _ _ _ _ _ (eq_symm (.conjR hE)) (left_subst _ _ _ _ _ (eq_symm (.conjL hE)) hp2)

theorem exact_at_specialize {m} {Γ : Context m} (w p a b c d : Fin m) (hx : Derives Γ (exactAt w p a b)) :
    Derives Γ ((witness w p c d).iff ((Formula.equal c a).conj (.equal d b))) := by
  have h1 : Derives Γ (.all ((witness w.castSucc p.castSucc c.castSucc (Fin.last m)).iff
      ((Formula.equal c.castSucc a.castSucc).conj (.equal (Fin.last m) b.castSucc)))) := by
    simpa only [exactAt, Formula.iff, Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE c hx
  simpa only [Formula.iff, Formula.instantiate, Formula.rename, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE d h1

theorem intro_fiber {m} {Γ : Context m} (w p a b : Fin m) (hp : Derives Γ (witness w p a b))
    (hx : Derives Γ (exactAt w p a b)) : Derives Γ (fiber w p) := by
  apply Derives.exI a
  apply Derives.exI b
  simp only [Formula.instantiate, Formula.rename, witness_rename, exactAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hx

theorem intro_bounded {m} {Γ : Context m} (w p a b : Fin m) (hp : Derives Γ (witness w p a b))
    (hx : Derives Γ (exactAt w p a b)) (hb : Derives Γ ((Formula.mem a p).conj (Formula.mem b p))) : Derives Γ (boundedFiber w p) := by
  apply Derives.exI a
  apply Derives.exI b
  simp only [Formula.instantiate, Formula.rename, witness_rename, exactAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hp hx) hb

theorem unique_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hpos : Derives Γ (empty p).neg) : Derives Γ (fiber w p) := by
  let W := witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_preimage w p _ (StructuralNodeDecodeExistence.preimage_exists hZ w p hw hp hpos)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ W
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw W
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hx := exact_at hZ2 _ _ _ _ hw2 hW
  have hout := intro_fiber _ _ _ _ hW hx
  simpa only [Formula.raise, fiber_rename] using hout

theorem bounded_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hpos : Derives Γ (empty p).neg) : Derives Γ (boundedFiber w p) := by
  let W := witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_preimage w p _ (StructuralNodeDecodeExistence.preimage_exists hZ w p hw hp hpos)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ W
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw W
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hx := exact_at hZ2 _ _ _ _ hw2 hW
  have hb := StructuralNodeProperties.components hZ2 _ _ _ _ hw2 (.conjL (.conjL hW)) (.conjR (.conjL hW)) (.conjR hW)
  have hout := intro_bounded _ _ _ _ hW hx hb
  simpa only [Formula.raise, boundedFiber_rename] using hout
end PPAC.Migration.Internal.StructuralNodeDecodeUnique
