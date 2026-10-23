import PPAC.Migration.Internal.SyntaxMixedFormulaOutput
import PPAC.Migration.Internal.SyntaxRenameBinders

/-! 已知原源构造时，异标签的所有混合替换分支由原构造器标签单射正式排除。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaBranchReject
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxRenameQuerySyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (tag : Nat) (advance : Bool)
    (hne : label ≠ tag) (w r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity label w xs n))
    (hr : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w r s a b c d n q)) : Derives Γ .bot := by
  let B := SyntaxMixedFormulaRecursiveSyntax.singleBody tag advance w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_2 B _ hr
  have hZk := zf_under_2 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hck : Derives Δ (constructor arity label w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename]) (under_2 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZk arity 1 label tag hne w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (fun _ => (Fin.last m).castSucc) n.castSucc.castSucc hwk hck (.conjL hB)

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (kind : Fin 4)
    (hne : label ≠ (SyntaxLogicalSyntax.binaryTag kind)) (w r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity label w xs n))
    (hr : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w r s a b c d n q)) : Derives Γ .bot := by
  let B := SyntaxMixedFormulaRecursiveSyntax.binaryBody kind w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ hr
  have hZk := zf_under_4 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hck : Derives Δ (constructor arity label w.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename]) (under_4 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZk arity 2 label (SyntaxLogicalSyntax.binaryTag kind) hne w.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc) (SyntaxAtomSyntax.two (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc hwk hck (.conjL hB)

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat)
    (hne : label ≠ 2) (w r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity label w xs n))
    (hr : Derives Γ (SyntaxMixedFormulaAtomSyntax.membership w r s a b c d n q)) : Derives Γ .bot := by
  let B := SyntaxMixedFormulaAtomSyntax.membershipBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))
  apply eliminate_5 B _ hr
  have hZk := zf_under_5 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_5 hw B)
  have hck : Derives Δ (constructor arity label w.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename]) (under_5 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZk arity 3 label 2 hne w.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc.castSucc) (SyntaxAtomSyntax.three (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc.castSucc hwk hck (.conjL (.conjR hB))

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat)
    (hne : label ≠ 3) (w r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity label w xs n))
    (hr : Derives Γ (SyntaxMixedFormulaAtomSyntax.equality w r s a b c d n q)) : Derives Γ .bot := by
  let B := SyntaxMixedFormulaAtomSyntax.equalityBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ hr
  have hZk := zf_under_4 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hck : Derives Δ (constructor arity label w.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename]) (under_4 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZk arity 2 label 3 hne w.castSucc.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc.castSucc) (SyntaxAtomSyntax.two (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) n.castSucc.castSucc.castSucc.castSucc hwk hck (.conjL hB)

end PPAC.Migration.Internal.SyntaxMixedFormulaBranchReject
