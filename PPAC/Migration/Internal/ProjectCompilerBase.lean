import PPAC.Migration.Internal.ProjectCompilerCaseIntro

/-! Actual compiler execution of both constants and all three Project atomic modes. -/
namespace PPAC.Migration.Internal.ProjectCompilerBase
open Source SourceAlgebra SourceLogic OmegaSyntax
open ProjectCompilerLocalSyntax (readMatrix one)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def existsTyped {m} (w n b z : Fin m) : Formula m := .ex
  ((ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc))

theorem existsTyped_rename {m l} (w n b z : Fin m) (ρ : Fin m → Fin l) :
    (existsTyped w n b z).rename ρ = existsTyped (ρ w) (ρ n) (ρ b) (ρ z) := by
  simp only [existsTyped, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename, FormulaCodeSyntax.formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem constant_histories {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b z : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (ProjectCompilerIndependent.allHistories w n b n) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n hw hc
  apply Derives.allI
  have hn1 : Derives (Context.image Formula.raise Γ) (.mem n.castSucc w.castSucc) := Derives.rename Fin.castSucc hn
  have hb1 : Derives (Context.image Formula.raise Γ) (.mem b.castSucc w.castSucc) := Derives.rename Fin.castSucc hb
  have hz1 := of_eq (empty_rename z Fin.castSucc) (Derives.rename Fin.castSucc hz)
  have hc1 : Derives (Context.image Formula.raise Γ)
      (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w.castSucc Fin.elim0 n.castSucc) := by
    simpa only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map] using Derives.rename Fin.castSucc hc
  have hi := ProjectCompilerCaseIntro.constant_cases truth readMatrix (one (Fin.last m)) w.castSucc b.castSucc z.castSucc n.castSucc n.castSucc (.conjI hc1 (.eqRefl n.castSucc))
  exact ProjectCompilerLocalSyntax.intro_local w.castSucc b.castSucc n.castSucc (Fin.last m) n.castSucc z.castSucc hn1 (.conjI hb1 hn1) hz1 hi

theorem constant_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b z : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b n) :=
  ProjectCompilerIndependent.compiled hZ w n b n hw
    (SyntaxNodeInjective.constructor_range hZ 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n hw hc)
    (constant_histories hZ truth w n b z hw hb hz hc)

theorem constant_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b n) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (Derives.conjL (Derives.conjL hw))
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w.castSucc Fin.elim0 n.castSucc) := by
    simpa only [Formula.raise, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map] using under hc Z
  have ho := constant_at_zero (ZFContext.under hZ Z) truth w.castSucc n.castSucc b.castSucc (Fin.last m) hw1 (under hb Z) (.conjR hZ0) hc1
  exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b n Fin.castSucc).symm ho

theorem atomic_histories {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) :
    Derives Γ (ProjectCompilerIndependent.allHistories w n b q) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 2 (ProjectAtomicSyntax.sourceTag kind) w (SyntaxAtomSyntax.two x y) n hw (.conjR (.conjR (.conjR (.conjL hc))))
  have hq := FormulaCodeProperties.guards w q b z (ProjectAtomicLaws.compiled_type hZ kind w b z x y n q hw hz hc)
  apply Derives.allI
  have hn1 : Derives (Context.image Formula.raise Γ) (.mem n.castSucc w.castSucc) := Derives.rename Fin.castSucc hn
  have hb1 : Derives (Context.image Formula.raise Γ) (.mem b.castSucc w.castSucc) := Derives.rename Fin.castSucc (Derives.conjL (Derives.conjL hc))
  have hq1 : Derives (Context.image Formula.raise Γ) (.mem q.castSucc w.castSucc) := Derives.rename Fin.castSucc (Derives.conjL hq)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (Derives.rename Fin.castSucc hz)
  have hc1 := of_eq (ProjectAtomicSyntax.compiled_rename kind w b z x y n q Fin.castSucc) (Derives.rename Fin.castSucc hc)
  have ha := ProjectCompilerCaseIntro.atomic_case kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc q.castSucc hc1
  have hi := ProjectCompilerCaseIntro.atomic_cases kind readMatrix (one (Fin.last m)) w.castSucc b.castSucc z.castSucc n.castSucc q.castSucc ha
  exact ProjectCompilerLocalSyntax.intro_local w.castSucc b.castSucc q.castSucc (Fin.last m) n.castSucc z.castSucc hn1 (.conjI hb1 hq1) hz1 hi

theorem atomic_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) :=
  ProjectCompilerIndependent.compiled hZ w n b q hw
    (SyntaxNodeInjective.constructor_range hZ 2 (ProjectAtomicSyntax.sourceTag kind) w (SyntaxAtomSyntax.two x y) n hw (.conjR (.conjR (.conjR (.conjL hc)))))
    (atomic_histories hZ kind w b z x y n q hw hz hc)

theorem atomic_exists_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z x y n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (ProjectAtomicSyntax.sourceAt kind w b x y n)) :
    Derives Γ (existsTyped w n b z) := by
  let A := ((((Formula.mem (Fin.last m) w.castSucc).conj
    (ProjectAtomicSyntax.compiled kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m))).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)).conj
        (ProjectAtomicSyntax.uniqueOutput kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m)))
  let Δ := Context.add A (Context.image Formula.raise Γ)
  apply Derives.exE (p := A) (ProjectAtomicExistence.exists_unique_typed hZ kind w b z x y n hw hz hi)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw A)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz A)
  have hc := atomic_compiled (ZFContext.under hZ A) kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m) hw1 hz1 (.conjR (.conjL (.conjL hA)))
  have ho : Derives Δ (existsTyped w.castSucc n.castSucc b.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hc (.conjR (.conjL hA)))
  exact of_eq (existsTyped_rename w n b z Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectCompilerBase
