import PPAC.Migration.Internal.ProjectCompilerCompleteFields

/-! Every independent Project source atom actually obtains a recursive compiler output. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCompleteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem of_typed {m} {Γ : Context m} (w n b z : Fin m) (he : Derives Γ (ProjectCompilerBase.existsTyped w n b z)) :
    Derives Γ (existsOutput w n b) := by
  let B := (ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (existsOutput_rename w n b Fin.castSucc).symm
    (intro_output w.castSucc n.castSucc b.castSucc (Fin.last m) (.conjL hB))

theorem nullary_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.nullary truth w b f n)) :
    Derives Γ (existsOutput w n b) :=
  intro_output w n b n (ProjectCompilerBase.constant_compiled hZ truth w n b hw (.conjL (.conjL hc)) (.conjR hc))

theorem binary_atom_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w n b z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectSourceAtomSyntax.binaryAtom kind w b n)) :
    Derives Γ (existsOutput w n b) := by
  let B := ProjectSourceAtomSyntax.binaryBody kind w b n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have he := ProjectCompilerBase.atomic_exists_typed (HornBinderRules.zf_body 2 hZ B) kind
    (old 2 w) (old 2 b) (old 2 z) (slot 2 0) (slot 2 1) (old 2 n) hw2 hz2 hB
  exact of_eq (existsOutput_rename w n b (old 2)).symm (of_typed (old 2 w) (old 2 n) (old 2 b) (old 2 z) he)

theorem all_atoms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectSourceAtomSyntax.atomic w b f n)) :
    Derives Γ (existsOutput w n b) := by
  have h0 : Derives Γ ((SyntaxAtomSyntax.nullary false w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact nullary_output (ZFContext.add hZ _) false w n b f (add hw _) (.hyp (Or.inl rfl))
  have h1 : Derives Γ ((SyntaxAtomSyntax.nullary true w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact nullary_output (ZFContext.add hZ _) true w n b f (add hw _) (.hyp (Or.inl rfl))
  have hb0 : Derives Γ ((ProjectSourceAtomSyntax.binaryAtom 0 w b n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_atom_output (ZFContext.add hZ _) 0 w n b z (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have hb1 : Derives Γ ((ProjectSourceAtomSyntax.binaryAtom 1 w b n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_atom_output (ZFContext.add hZ _) 1 w n b z (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have hb2 : Derives Γ ((ProjectSourceAtomSyntax.binaryAtom 2 w b n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_atom_output (ZFContext.add hZ _) 2 w n b z (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have hall := FormulaCodeCaseLogic.disj_imp hb0 (FormulaCodeCaseLogic.disj_imp hb1 hb2)
  have hright : Derives Γ (((SyntaxTermSyntax.contexts w b f).conj
      ((ProjectSourceAtomSyntax.binaryAtom 0 w b n).disj ((ProjectSourceAtomSyntax.binaryAtom 1 w b n).disj (ProjectSourceAtomSyntax.binaryAtom 2 w b n)))).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact .impE (add hall _) (.conjR (.hyp (Or.inl rfl)))
  exact .impE (FormulaCodeCaseLogic.disj_imp (FormulaCodeCaseLogic.disj_imp h0 h1) hright) hc

end PPAC.Migration.Internal.ProjectCompilerCompleteAtoms
