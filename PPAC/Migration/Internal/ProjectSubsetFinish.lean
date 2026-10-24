import PPAC.Migration.Internal.ProjectSubsetLaws
import PPAC.Migration.Internal.ProjectSubsetAssembly

/-! A named boundary separates preparation from the four actual output constructors. -/
namespace PPAC.Migration.Internal.ProjectSubsetFinish
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def prepared {m} (w b z x y : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (successor (env 0) b).conj ((ProjectBoundShiftSyntax.shifted w x (env 1)).conj
    ((ProjectBoundShiftSyntax.shifted w y (env 2)).conj
      ((SyntaxVariableSyntax.code true w z (env 3)).conj (SyntaxAtomSyntax.zeroScalar w (env 4)))))

theorem prepared_rename {m l} (w b z x y : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (prepared w b z x y env).rename ρ = prepared (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (fun i => ρ (env i)) := by
  simp only [prepared, Formula.rename, successor_rename, ProjectBoundShiftSyntax.shifted_rename,
    SyntaxVariableSyntax.code_rename, SyntaxAtomSyntax.zeroScalar_rename]

theorem finish {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b z x y : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (prepared w b z x y env)) : Derives Γ (ProjectSubsetSyntax.existsOutput w b z x y) := by
  have hnX := ProjectBoundShiftLaws.range hZ w x (env 1) hw (.conjL (.conjR hp))
  have hnY := ProjectBoundShiftLaws.range hZ w y (env 2) hw (.conjL (.conjR (.conjR hp)))
  have hnV := SyntaxVariableDecode.range hZ true w z (env 3) hw (.conjL (.conjR (.conjR (.conjR hp))))
  have hnS := SyntaxNodeInjective.constructor_range hZ 0 0 w Fin.elim0 (env 4) hw (.conjR (.conjR (.conjR (.conjR hp))))
  let K0 := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 2 w.castSucc (SyntaxAtomSyntax.three (env 4).castSucc (env 3).castSucc (env 1).castSucc) (Fin.last m))
  let Γ1 := Context.add K0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := K0) (SyntaxConstructors.exists_constructor hZ 3 2 w (SyntaxAtomSyntax.three (env 4) (env 3) (env 1)) hw (.conjI hnS (.conjI hnV (.conjI hnX (.eqRefl w)))))
  have hK0 : Derives Γ1 K0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ K0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K0)
  let K1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 3 2 w.castSucc.castSucc (SyntaxAtomSyntax.three (env 4).castSucc.castSucc (env 3).castSucc.castSucc (env 2).castSucc.castSucc) (Fin.last (m+1)))
  let Γ2 := Context.add K1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := K1) (SyntaxConstructors.exists_constructor hZ1 3 2 w.castSucc (SyntaxAtomSyntax.three (env 4).castSucc (env 3).castSucc (env 2).castSucc) hw1 (.conjI (under hnS K0) (.conjI (under hnV K0) (.conjI (under hnY K0) (.eqRefl w.castSucc)))))
  have hK1 : Derives Γ2 K1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 K1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 K1)
  let K2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) (Fin.last (m+2)))
  let Γ3 := Context.add K2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := K2) (SyntaxConstructors.exists_constructor hZ2 2 7 w.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc (Fin.last (m+1))) hw2 (.conjI (under (Derives.conjL hK0) K1) (.conjI (Derives.conjL hK1) (.eqRefl w.castSucc.castSucc))))
  have hK2 : Derives Γ3 K2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 K2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 K2)
  let K3 := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj
    (SyntaxNodeSyntax.constructor 1 9 w.castSucc.castSucc.castSucc.castSucc (fun _ => (Fin.last (m+2)).castSucc) (Fin.last (m+3)))
  let Γ4 := Context.add K3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := K3) (SyntaxConstructors.exists_constructor hZ3 1 9 w.castSucc.castSucc.castSucc (fun _ => (Fin.last (m+2))) hw3 (.conjI (Derives.conjL hK2) (.eqRefl w.castSucc.castSucc.castSucc)))
  have hK3 : Derives Γ4 K3 := .hyp (Or.inl rfl)
  have hp4 : Derives Γ4 (prepared w.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [Formula.raise, prepared_rename] using (under (under (under (under hp K0) K1) K2) K3)
  have hC0 : Derives Γ4 (SyntaxNodeSyntax.constructor 3 2 w.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.three (env 4).castSucc.castSucc.castSucc.castSucc (env 3).castSucc.castSucc.castSucc.castSucc (env 1).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map] using (under (under (under (Derives.conjR hK0) K1) K2) K3)
  have hC1 : Derives Γ4 (SyntaxNodeSyntax.constructor 3 2 w.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.three (env 4).castSucc.castSucc.castSucc.castSucc (env 3).castSucc.castSucc.castSucc.castSucc (env 2).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map] using (under (under (Derives.conjR hK1) K2) K3)
  have hC2 : Derives Γ4 (SyntaxNodeSyntax.constructor 2 7 w.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) (Fin.last (m+2)).castSucc) := by
    simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map] using (under (Derives.conjR hK2) K3)
  have hC3 : Derives Γ4 (SyntaxNodeSyntax.constructor 1 9 w.castSucc.castSucc.castSucc.castSucc (fun _ => (Fin.last (m+2)).castSucc) (Fin.last (m+3))) := by
    exact Derives.conjR hK3
  have he := ProjectSubsetAssembly.assemble (Γ := Γ4) w.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (env 0).castSucc.castSucc.castSucc.castSucc (env 1).castSucc.castSucc.castSucc.castSucc (env 2).castSucc.castSucc.castSucc.castSucc (env 3).castSucc.castSucc.castSucc.castSucc (env 4).castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjL hp4) (.conjL (.conjR hp4)) (.conjL (.conjR (.conjR hp4))) (.conjL (.conjR (.conjR (.conjR hp4)))) (.conjR (.conjR (.conjR (.conjR hp4)))) hC0 hC1 hC2 hC3
  have ho := ProjectSubsetSyntax.intro_exists w.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (.conjL hK3) he
  exact of_eq (by simp only [Formula.raise, ProjectSubsetSyntax.existsOutput_rename]) ho

end PPAC.Migration.Internal.ProjectSubsetFinish
