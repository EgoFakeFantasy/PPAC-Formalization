import PPAC.Migration.Internal.SyntaxMixedFormulaAtomConstruct

/-! 两类非空原子的实际输出码纤维；合法混合环境在对象层量化。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaAtomOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxAtomSyntax SyntaxMixedFormulaOutputSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q v x y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (equalCode w x y n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))
    (hv : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := SyntaxMixedFormulaCases.atomic_of_substituted hZ 3 2 w R S a b c d n q (two x y) hw hc hq
  have h2 := SyntaxMixedFormulaCases.atomic_of_substituted hZ 3 2 w R S a b c d n v (two x y) hw hc hv
  exact SyntaxMixedFormulaAtomUnique.equality_unique hZ w R S a b c d n q v hw h1 h2

theorem equality_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hc : Derives Γ (equalCode w x y n)) : Derives Γ (fiber w R S a b c d n) := by
  have he := SyntaxMixedFormulaAtomConstruct.equality_exists hZ w R S a b c d n x y hw hi hc
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have hc2 : Derives Δ (equalCode w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, equalCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Q, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hQ V)
    exact equality_unique hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem equality_property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have hc6 : Derives Δ (equalCode w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, equalCode_rename]) (under_6 hc I)
  exact equality_fiber (zf_under_6 hZ I) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6

theorem membership_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q v z x y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (memberCode w z x y n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))
    (hv : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := SyntaxMixedFormulaCases.atomic_of_substituted hZ 2 3 w R S a b c d n q (three z x y) hw hc hq
  have h2 := SyntaxMixedFormulaCases.atomic_of_substituted hZ 2 3 w R S a b c d n v (three z x y) hw hc hv
  exact SyntaxMixedFormulaAtomUnique.membership_unique hZ w R S a b c d n q v hw h1 h2

theorem membership_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (fiber w R S a b c d n) := by
  have he := SyntaxMixedFormulaAtomConstruct.membership_exists hZ w R S a b c d n z x y hw hi hc
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let V := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) Q) V)
    have hc2 : Derives Δ (memberCode w.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, memberCode_rename]) (under (under (hc) Q) V)
    have hGiven : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) :=
      of_eq (by simp only [Q, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hQ V)
    exact membership_unique hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc hw2 hc2 (.hyp (Or.inl rfl)) hGiven
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w R S a b c d n Fin.castSucc).symm ho

theorem membership_property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z x y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w z x y n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have hc6 : Derives Δ (memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, memberCode_rename]) (under_6 hc I)
  exact membership_fiber (zf_under_6 hZ I) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6

end PPAC.Migration.Internal.SyntaxMixedFormulaAtomOutput
