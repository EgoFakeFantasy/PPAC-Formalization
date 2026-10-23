import PPAC.Migration.Internal.SyntaxCodedMixedBinderTyping

/-! 原数值混合binder的实际唯一输出码对纤维及精确纯输入双条件。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def uniquePair {m} (w R S a b c d A C K H : Fin m) : Formula m := .all (.all
  ((lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((Formula.equal K.castSucc.castSucc (Fin.last m).castSucc).conj (Formula.equal H.castSucc.castSucc (Fin.last (m+1))))))

def fiberTail {m} (w R S a b c d A C K : Fin m) : Formula m := .ex
  ((lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc (Fin.last m)).conj (uniquePair w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc (Fin.last m)))

def fiber {m} (w R S a b c d A C : Fin m) : Formula m := .ex (fiberTail w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m))

theorem uniquePair_rename {m j} (w R S a b c d A C K H : Fin m) (ρ : Fin m → Fin j) :
    (uniquePair w R S a b c d A C K H).rename ρ = uniquePair (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) (ρ H) := by
  simp only [uniquePair, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiberTail_rename {m j} (w R S a b c d A C K : Fin m) (ρ : Fin m → Fin j) :
    (fiberTail w R S a b c d A C K).rename ρ = fiberTail (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) := by
  simp only [fiberTail, Formula.rename, lifted_rename, uniquePair_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m j} (w R S a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (fiber w R S a b c d A C).rename ρ = fiber (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [fiber, Formula.rename, fiberTail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (uniquePair w R S a b c d A C K H) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let V := lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw V)
  have hl2 : Derives Δ (lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 hl V)
  exact SyntaxCodedMixedBinderUnique.unique_pair (SyntaxRenameBinders.zf_under_2 hZ V) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hl2 (.hyp (Or.inl rfl))

theorem intro_fiber {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hl : Derives Γ (lifted w R S a b c d A C K H)) (hu : Derives Γ (uniquePair w R S a b c d A C K H)) : Derives Γ (fiber w R S a b c d A C) := by
  apply Derives.exI K
  apply Derives.exI H
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, lifted_rename, uniquePair_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hl hu)

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d A C)) : Derives Γ (fiber w R S a b c d A C) := by
  let B := lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex B)) := SyntaxCodedMixedBinderExistence.exists_pair hZ w R S a b c d A C hw hi
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := unique_pair (SyntaxRenameBinders.zf_under_2 hZ B) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB
  have ho := intro_fiber w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hB hu
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsPair w R S a b c d A C).iff (input w R S a b c d A C)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsPair w R S a b c d A C
    let B := lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    have he : Derives (Context.add E Γ) (.ex (.ex B)) := .hyp (Or.inl rfl)
    apply SyntaxRenameBinders.eliminate_2 B _ he
    have ho := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (Derives.hyp (Or.inl rfl) : Derives Δ B)
    exact of_eq (by simp only [Formula.raise, input_rename]) ho
  · apply Derives.impI
    let I := input w R S a b c d A C
    have hi : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    exact SyntaxCodedMixedBinderExistence.exists_pair (ZFContext.add hZ I) w R S a b c d A C (add hw I) hi

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w R S a b c d A C).iff (input w R S a b c d A C)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := fiber w R S a b c d A C
    let B := (lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj (uniquePair w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    have he : Derives (Context.add E Γ) (.ex (.ex B)) := .hyp (Or.inl rfl)
    apply SyntaxRenameBinders.eliminate_2 B _ he
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hB)
    exact of_eq (by simp only [Formula.raise, input_rename]) ho
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w R S a b c d A C (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxCodedMixedBinderFiber
