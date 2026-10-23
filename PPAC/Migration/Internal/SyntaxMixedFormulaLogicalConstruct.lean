import PPAC.Migration.Internal.SyntaxMixedFormulaCheckExistence

/-! 七类合法原逻辑模式从实际子输出生成真实目标原构造及 MixedFormulaSubst；不预设父输出。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w b f x n : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.singleTypes advance w b f x)) := by
  rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact FormulaCodeKnownLogical.negation_iff hZ w b f x n hw hc
  · exact FormulaCodeKnownLogical.forall_iff hZ w b f x n hw hc
  · exact FormulaCodeKnownLogical.exists_iff hZ w b f x n hw hc

theorem binary_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w b f x y n : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.binaryTypes w b f x y)) := by
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact FormulaCodeKnownLogical.binary0_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary1_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary2_iff hZ w b f x y n hw hc
  · exact FormulaCodeKnownLogical.binary3_iff hZ w b f x y n hw hc

theorem single_at_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x X : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (singleCode tag w x n))
    (hx : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x R S a b c d X)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w c d) := .conjL (.conjR (.conjL (.conjR hi)))
  have hxN := SyntaxMixedFormulaCheckUnique.natural advance w x R S a b c d X hx
  have hb := SyntaxLogicalFields.single_bound hZ tag w x n hw hc
  have hI : Derives Γ (SyntaxForestSyntax.inputs 1 w (fun _ => X)) := .conjI hxN (.eqRefl w)
  have he := SyntaxConstructors.exists_constructor hZ 1 tag w (fun _ => X) hw hI
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (singleCode tag w.castSucc X.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex Q) := of_eq (by simp only [Q, SyntaxNodeSyntax.existsConstructor, singleCode]) he
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under hw Q)
  have hi1 : Derives Δ (input w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under hi Q)
  have hc1 : Derives Δ (singleCode tag w.castSucc x.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (under hc Q)
  have hctx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc d.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (under hctx Q)
  have hx1 : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc X.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.check_rename]) (under hx Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hb1 : Derives Δ (.mem x.castSucc n.castSucc) := under hb Q
  have htX := SyntaxMixedFormulaCheckUnique.target_type advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc X.castSucc hx1
  have ht := Derives.impE (.conjR (single_types hZ1 tag advance valid w.castSucc c.castSucc d.castSucc X.castSucc (Fin.last m) hw1 (.conjR hQ))) (.conjI hctx1 htX)
  have hd : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc) := .conjI hc1 (.conjI hb1 (.conjI (.conjR hQ) hx1))
  have ha := SyntaxMixedFormulaRecursiveSyntax.intro_single tag advance w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc X.castSucc hd
  have hCases : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .disjR (.disjR (.disjR (.disjL ha)))
    · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL ha))))))))
    · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (ha)))))))))
  have hout := SyntaxMixedFormulaCases.intro_from_cases hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hi1 ht hCases
  have ho := intro_exists w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hout
  exact of_eq (existsOutput_rename w R S a b c d n Fin.castSucc).symm ho

theorem binary_at_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (binaryCode kind w x y n))
    (hx : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w c d) := .conjL (.conjR (.conjL (.conjR hi)))
  have hxN := SyntaxMixedFormulaOutput.output_natural w R S a b c d x X hx
  have hyN := SyntaxMixedFormulaOutput.output_natural w R S a b c d y Y hy
  have hb := SyntaxLogicalFields.binary_bounds hZ kind w x y n hw hc
  have hI : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two X Y)) := .conjI hxN (.conjI hyN (.eqRefl w))
  have he := SyntaxConstructors.exists_constructor hZ 2 (binaryTag kind) w (SyntaxAtomSyntax.two X Y) hw hI
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (binaryCode kind w.castSucc X.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hex : Derives Γ (.ex Q) := of_eq (by simp only [Q, SyntaxNodeSyntax.existsConstructor, binaryCode, SyntaxAtomSyntax.two_map]) he
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under hw Q)
  have hi1 : Derives Δ (input w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under hi Q)
  have hc1 : Derives Δ (binaryCode kind w.castSucc x.castSucc y.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (under hc Q)
  have hctx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc d.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (under hctx Q)
  have hx1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hx Q)
  have hy1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hy Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hb1 : Derives Δ ((Formula.mem x.castSucc n.castSucc).conj (.mem y.castSucc n.castSucc)) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hb Q)
  have htX := SyntaxMixedFormulaJudgment.target_type w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc X.castSucc hx1
  have htY := SyntaxMixedFormulaJudgment.target_type w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc y.castSucc Y.castSucc hy1
  have ht := Derives.impE (.conjR (binary_types hZ1 kind w.castSucc c.castSucc d.castSucc X.castSucc Y.castSucc (Fin.last m) hw1 (.conjR hQ))) (.conjI hctx1 (.conjI htX htY))
  have hd : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc) := .conjI hc1 (.conjI (.conjL hb1) (.conjI (.conjR hb1) (.conjI (.conjR hQ) (.conjI hx1 hy1))))
  have ha := SyntaxMixedFormulaRecursiveSyntax.intro_binary kind w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) x.castSucc y.castSucc X.castSucc Y.castSucc hd
  have hCases : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.cases w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)) := by
    have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact .disjR (.disjR (.disjR (.disjR (.disjL ha))))
    · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjL ha)))))
    · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL ha))))))
    · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL ha)))))))
  have hout := SyntaxMixedFormulaCases.intro_from_cases hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hi1 ht hCases
  have ho := intro_exists w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hout
  exact of_eq (existsOutput_rename w R S a b c d n Fin.castSucc).symm ho

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalConstruct
