import PPAC.Migration.Internal.SyntaxLogicalTyping

/-! 给定真实子码和历史状态读取，实际构造七种逻辑节点；保留给定子字段。 -/
namespace PPAC.Migration.Internal.SyntaxLogicalExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxLogicalSyntax SyntaxContextReadSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h x : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (contexts w b f)) (hx : Derives Γ (.mem x w))
    (hr : Derives Γ (check advance h x b f)) : Derives Γ (existsSingle tag advance w b f h x) := by
  have hi : Derives Γ (inputs 1 w (fun _ => x)) := .conjI hx (.eqRefl _)
  have he := SyntaxConstructors.exists_constructor hZ 1 tag w (fun _ => x) hw hi
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (singleCode tag w.castSucc x.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have heN : Derives Γ (.ex N) := he
  apply Derives.exE (p := N) heN
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hc1 : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by simpa only [Formula.raise, contexts_rename] using under hc N
  have hr1 : Derives Δ (check advance h.castSucc x.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, check_rename] using under hr N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hb := SyntaxConstructors.child_member hZ1 1 tag _ (fun _ => x.castSucc) _ 0 hw1 (.conjR hN)
  have hd := intro_single tag advance _ _ _ _ x.castSucc _ hc1 (.conjI (.conjR hN) (.conjI hb hr1))
  have hout : Derives Δ (existsSingle tag advance w.castSucc b.castSucc f.castSucc h.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, single_rename, singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) (.conjI hd (.conjR hN))
  simpa only [Formula.raise, existsSingle_rename] using hout

theorem binary_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (contexts w b f)) (hx : Derives Γ (.mem x w)) (hy : Derives Γ (.mem y w))
    (hr : Derives Γ ((read h x b f).conj (read h y b f))) : Derives Γ (existsBinary kind w b f h x y) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI hx (.conjI hy (.eqRefl _))
  have he := SyntaxConstructors.exists_constructor hZ 2 (binaryTag kind) w (two x y) hw hi
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (binaryCode kind w.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have heN : Derives Γ (.ex N) := by simpa only [N, existsConstructor, binaryCode, two_map] using he
  apply Derives.exE (p := N) heN
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hc1 : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by simpa only [Formula.raise, contexts_rename] using under hc N
  have hr1 : Derives Δ ((read h.castSucc x.castSucc b.castSucc f.castSucc).conj (read h.castSucc y.castSucc b.castSucc f.castSucc)) := by
    simpa only [Formula.raise, Formula.rename, read_rename] using under hr N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hxB := SyntaxConstructors.child_member hZ1 2 (binaryTag kind) _ (two x.castSucc y.castSucc) _ 0 hw1 (.conjR hN)
  have hyB := SyntaxConstructors.child_member hZ1 2 (binaryTag kind) _ (two x.castSucc y.castSucc) _ 1 hw1 (.conjR hN)
  have hd := intro_binary kind _ _ _ _ x.castSucc y.castSucc _ hc1 (.conjI (.conjR hN) (.conjI hxB (.conjI hyB hr1)))
  have hout : Derives Δ (existsBinary kind w.castSucc b.castSucc f.castSucc h.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, binary_rename, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hN) (.conjI hd (.conjR hN))
  simpa only [Formula.raise, existsBinary_rename] using hout

theorem quantified_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w b f h x k : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (contexts w b f)) (hx : Derives Γ (.mem x w))
    (hk : Derives Γ (successor k b)) (hr : Derives Γ (read h x k f)) :
    Derives Γ (existsSingle (quantifierTag universal) true w b f h x) :=
  single_exists hZ (quantifierTag universal) true w b f h x hw hc hx (intro_advanced h x b f k hk hr)
end PPAC.Migration.Internal.SyntaxLogicalExistence
