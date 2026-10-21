import PPAC.Migration.Internal.SyntaxLogicalExistence

/-! 逻辑原构造码的全部字段恢复、严格子码界、根范围及同输入码唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxLogicalFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x y n : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (singleCode tag w x n)) (hy : Derives Γ (singleCode tag w y n)) : Derives Γ (.equal x y) :=
  SyntaxNodeInjective.constructor_input_eq hZ 1 tag tag w (fun _ => x) (fun _ => y) n 0 hw hx hy

theorem binary_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w x y u v n : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (binaryCode kind w x y n)) (hy : Derives Γ (binaryCode kind w u v n)) :
    Derives Γ ((Formula.equal x u).conj (.equal y v)) :=
  .conjI (SyntaxNodeInjective.constructor_input_eq hZ 2 (binaryTag kind) (binaryTag kind) w (two x y) (two u v) n 0 hw hx hy)
    (SyntaxNodeInjective.constructor_input_eq hZ 2 (binaryTag kind) (binaryTag kind) w (two x y) (two u v) n 1 hw hx hy)

theorem single_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n)) : Derives Γ (.mem x n) :=
  SyntaxConstructors.child_member hZ 1 tag w (fun _ => x) n 0 hw hc

theorem binary_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) : Derives Γ ((Formula.mem x n).conj (.mem y n)) :=
  .conjI (SyntaxConstructors.child_member hZ 2 (binaryTag kind) w (two x y) n 0 hw hc)
    (SyntaxConstructors.child_member hZ 2 (binaryTag kind) w (two x y) n 1 hw hc)

theorem single_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (singleCode tag w x n)) (hr : Derives Γ (singleCode tag w x r)) : Derives Γ (.equal n r) :=
  SyntaxConstructors.unique hZ 1 tag w (fun _ => x) n r hw hn hr

theorem binary_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w x y n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (binaryCode kind w x y n)) (hr : Derives Γ (binaryCode kind w x y r)) : Derives Γ (.equal n r) :=
  SyntaxConstructors.unique hZ 2 (binaryTag kind) w (two x y) n r hw hn hr

theorem single_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (single tag advance w b f h n)) : Derives Γ (.mem n w) := by
  let C := singleBody tag advance w b f h n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (ZFContext.under hZ C) 1 tag _ _ _ hw1 (.conjL hC)

theorem binary_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (binary kind w b f h n)) : Derives Γ (.mem n w) := by
  let C := binaryBody kind w b f h n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (ZFContext.under_two hZ C) 2 (binaryTag kind) _ _ _ hw1 (.conjL hC)
end PPAC.Migration.Internal.SyntaxLogicalFields
