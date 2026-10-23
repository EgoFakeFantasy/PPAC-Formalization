import PPAC.Migration.Internal.SyntaxMixedFormulaAtomOutput

/-! 假/真空原子的实际自替换与全内部候选唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaNullary
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaJudgmentSyntax
open SyntaxMixedFormulaOutputSyntax SyntaxNodeSyntax SyntaxAtomSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem intro_self {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (substituted w r s a b c d n n) := by
  have hr := Derives.conjL (.conjR hi)
  have hs := Derives.conjR (.conjR hi)
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w c d) := .conjL (.conjR hr)
  have hsrc : Derives Γ (SyntaxTermSyntax.contexts w a b) := .conjI (.conjL hr) (.conjL hs)
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w c d n hw hc)) hctx
  have hA : Derives Γ (SyntaxMixedFormulaAtomSyntax.nullary truth w a b c d n n) :=
    .conjI (.conjI hsrc hc) (.conjI hctx hc)
  have hl : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w r s a b c d n n) := by
    cases truth
    · exact .disjL (.disjL hA)
    · exact .disjL (.disjR hA)
  exact SyntaxMixedFormulaCases.intro_from_cases hZ w r s a b c d n n hw hi ht hl

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n))
    (hr : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (.equal q n) := by
  have hA : Derives Γ (SyntaxMixedFormulaAtomSyntax.nullary truth w a b c d n q) := by
    cases truth
    · exact SyntaxMixedFormulaCases.atomic_of_substituted hZ 0 0 w r s a b c d n q Fin.elim0 hw hc hr
    · exact SyntaxMixedFormulaCases.atomic_of_substituted hZ 1 0 w r s a b c d n q Fin.elim0 hw hc hr
  exact SyntaxConstructors.unique hZ 0 (nullaryTag truth) w Fin.elim0 q n hw (.conjR (.conjR hA)) hc

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (fiber w r s a b c d n) := by
  have hself := intro_self hZ truth w r s a b c d n hw hi hc
  have hu : Derives Γ (uniqueOutput w r s a b c d n n) := by
    apply Derives.allI
    apply Derives.impI
    let Q := substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise Γ)
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
    have hc1 : Derives Δ (constructor 0 (nullaryTag truth) w.castSucc Fin.elim0 n.castSucc) :=
      of_eq (by simp only [Formula.raise, constructor_rename, zero_map]) (under hc Q)
    exact unique (ZFContext.under hZ Q) truth _ _ _ _ _ _ _ _ (Fin.last m) hw1 hc1 (.hyp (Or.inl rfl))
  exact intro_fiber w r s a b c d n n hself hu
theorem property_all_parameters {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (property w n) := by
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
  have hc6 : Derives Δ (constructor 0 (nullaryTag truth) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc Fin.elim0 n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, constructor_rename, zero_map]) (under_6 hc I)
  exact actual_fiber (zf_under_6 hZ I) truth w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 (.hyp (Or.inl rfl)) hc6
end PPAC.Migration.Internal.SyntaxMixedFormulaNullary
