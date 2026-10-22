import PPAC.Migration.Internal.SyntaxMixedImageBinderOutput

/-! 全内部混合binder的准确输入、实际唯一输出纤维；合法空域与非标准内部码不另排除。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageBinderFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def input {m} (w r s a b c d A C : Fin m) : Formula m :=
  (SyntaxTermImageSyntax.maps w r s a b c d).conj ((successor A a).conj (successor C c))

def uniquePair {m} (w r s a b c d A C k h : Fin m) : Formula m := .all (.all
  ((lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((Formula.equal k.castSucc.castSucc (Fin.last m).castSucc).conj (Formula.equal h.castSucc.castSucc (Fin.last (m+1))))))

def fiberTail {m} (w r s a b c d A C k : Fin m) : Formula m := .ex
  ((lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc (Fin.last m)).conj (uniquePair w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc (Fin.last m)))

def fiber {m} (w r s a b c d A C : Fin m) : Formula m := .ex (fiberTail w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m))

theorem input_rename {m j} (w r s a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (input w r s a b c d A C).rename ρ = input (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [input, Formula.rename, SyntaxTermImageSyntax.maps_rename, successor_rename]

theorem uniquePair_rename {m j} (w r s a b c d A C k h : Fin m) (ρ : Fin m → Fin j) :
    (uniquePair w r s a b c d A C k h).rename ρ = uniquePair (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ k) (ρ h) := by
  simp only [uniquePair, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiberTail_rename {m j} (w r s a b c d A C k : Fin m) (ρ : Fin m → Fin j) :
    (fiberTail w r s a b c d A C k).rename ρ = fiberTail (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ k) := by
  simp only [fiberTail, Formula.rename, lifted_rename, uniquePair_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m j} (w r s a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (fiber w r s a b c d A C).rename ρ = fiber (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [fiber, Formula.rename, fiberTail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_of_lifted {m} {Γ : Context m} (w r s a b c d A C k h : Fin m)
    (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ (input w r s a b c d A C) := by
  let B := body w r s a b c d A C k h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxMixedImageLiftFields.source_inputs w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR hB)))
  have ho : Derives Δ (input w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc) := .conjI (.conjL hi) (.conjI (.conjR hi) (.conjL (.conjL hB)))
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C k h : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ (uniquePair w r s a b c d A C k h) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let V := lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw V)
  have hl2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc k.castSucc.castSucc h.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 hl V)
  exact SyntaxMixedImageBinderOutput.unique_pair (SyntaxRenameBinders.zf_under_2 hZ V) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc k.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hl2 (.hyp (Or.inl rfl))

theorem intro_fiber {m} {Γ : Context m} (w r s a b c d A C k h : Fin m)
    (hl : Derives Γ (lifted w r s a b c d A C k h)) (hu : Derives Γ (uniquePair w r s a b c d A C k h)) : Derives Γ (fiber w r s a b c d A C) := by
  apply Derives.exI k
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, lifted_rename, uniquePair_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hl hu)

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d A C)) : Derives Γ (fiber w r s a b c d A C) := by
  let B := lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex B)) := SyntaxMixedImageBinderOutput.exists_pair hZ w r s a b c d A C hw (.conjL hi) (.conjL (.conjR hi)) (.conjR (.conjR hi))
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hu := unique_pair (SyntaxRenameBinders.zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB
  have ho := intro_fiber w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hB hu
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsPair w r s a b c d A C).iff (input w r s a b c d A C)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := existsPair w r s a b c d A C
    let B := lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    have he : Derives (Context.add E Γ) (.ex (.ex B)) := .hyp (Or.inl rfl)
    apply SyntaxRenameBinders.eliminate_2 B _ he
    have ho := input_of_lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (Derives.hyp (Or.inl rfl) : Derives Δ B)
    exact of_eq (by simp only [Formula.raise, input_rename]) ho
  · apply Derives.impI
    let I := input w r s a b c d A C
    have hi : Derives (Context.add I Γ) I := .hyp (Or.inl rfl)
    exact SyntaxMixedImageBinderOutput.exists_pair (ZFContext.add hZ I) w r s a b c d A C (add hw I) (.conjL hi) (.conjL (.conjR hi)) (.conjR (.conjR hi))

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d A C : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w r s a b c d A C).iff (input w r s a b c d A C)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := fiber w r s a b c d A C
    let B := (lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj (uniquePair w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    have he : Derives (Context.add E Γ) (.ex (.ex B)) := .hyp (Or.inl rfl)
    apply SyntaxRenameBinders.eliminate_2 B _ he
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := input_of_lifted w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hB)
    exact of_eq (by simp only [Formula.raise, input_rename]) ho
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w r s a b c d A C (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedImageBinderFiber
