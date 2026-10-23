import PPAC.Migration.Internal.TermTransformProgramValueSyntax

/-! 输入不合法即拒绝；合法输入实际取得唯一有类型输出，均在原对象推导关系内。 -/
namespace PPAC.Migration.Internal.TermTransformProgramValue
open Source SourceAlgebra SourceLogic OmegaSyntax TermTransformProgramSyntax TermTransformProgramValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem reject_environment {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hi : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg) :
    Derives Γ (checked w R S a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjL (.conjL (.hyp (Or.inl rfl))))

theorem reject_source {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hi : Derives Γ (SyntaxTermSyntax.term w a b n).neg) :
    Derives Γ (checked w R S a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjR (.conjL (.hyp (Or.inl rfl))))

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (checked w R S a b c d n q)) :
    Derives Γ (SyntaxTermSyntax.term w c d q) :=
  SyntaxCodedMixedTermTyping.target_type w R S a b c d n q
    (.impE (.conjL (TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n q hw)) hq)

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (checked w R S a b c d n q)) : Derives Γ (.mem q w) :=
  SyntaxCodedMixedTermTyping.output_natural w R S a b c d n q
    (.impE (.conjL (TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n q hw)) hq)

theorem reject_target {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.term w c d q).neg) :
    Derives Γ (checked w R S a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (target_type (ZFContext.add hZ _) w R S a b c d n q (add hw _) (.hyp (Or.inl rfl)))

theorem reject_output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (Formula.mem q w).neg) :
    Derives Γ (checked w R S a b c d n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (output_natural (ZFContext.add hZ _) w R S a b c d n q (add hw _) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (checked w R S a b c d n q))
    (hv : Derives Γ (checked w R S a b c d n v)) : Derives Γ (.equal q v) :=
  SyntaxCodedMixedTermUnique.unique hZ w R S a b c d n q v hw
    (.impE (.conjL (TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n q hw)) hq)
    (.impE (.conjL (TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n v hw)) hv)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (checked w R S a b c d n q)) : Derives Γ (uniqueOutput w R S a b c d n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (checked_rename w R S a b c d n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

theorem at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (checked w R S a b c d n q)) : Derives Γ (value w R S a b c d n q) :=
  .conjI hq (.conjI (target_type hZ w R S a b c d n q hw hq)
    (.conjI (output_natural hZ w R S a b c d n q hw hq) (unique_output hZ w R S a b c d n q hw hq)))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputGuard w R S a b c d n)) : Derives Γ (fiber w R S a b c d n) := by
  have he := SyntaxCodedMixedTermExistence.exists_output hZ w R S a b c d n hw hi
  let Q := SyntaxCodedMixedTermSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hZ1 := ZFContext.under hZ Q
  have hq := Derives.impE (.conjR (TermTransformProgramCorrectness.checked_iff hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1)) (.hyp (Or.inl rfl))
  have ho := intro_fiber w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
    (at_candidate hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hq)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem input_of_fiber {m} {Γ : Context m} (w R S a b c d n : Fin m)
    (hf : Derives Γ (fiber w R S a b c d n)) : Derives Γ (inputGuard w R S a b c d n) := by
  let V := value w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hi : Derives Δ (inputGuard w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := .conjL (.conjL hV)
  exact of_eq (by simp only [Formula.raise, inputGuard_rename]) hi

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w R S a b c d n).iff (inputGuard w R S a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_fiber w R S a b c d n (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w R S a b c d n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.TermTransformProgramValue
