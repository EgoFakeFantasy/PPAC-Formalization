import PPAC.Migration.Internal.SyntaxRenameStateSyntax

/-! 七个内部自然字段的实际唯一状态码及全部反向字段恢复。 -/
namespace PPAC.Migration.Internal.SyntaxRenameState
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxRenameStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem legal_inputs {m} {Γ : Context m} (w r s a b c d q : Fin m) (hl : Derives Γ (legal w r s a b c d q)) :
    Derives Γ (inputs 7 w (seven r s a b c d q)) := by
  have hr := SyntaxMapCodeDecode.natural w a c r (.conjL hl)
  have hs := SyntaxMapCodeDecode.natural w b d s (.conjL (.conjR hl))
  have hc := SyntaxMapCodeDecode.contexts w a c r (.conjL hl)
  have hd := SyntaxMapCodeDecode.contexts w b d s (.conjL (.conjR hl))
  have hq := Derives.conjL (FormulaCodeProperties.guards w q c d (.conjR (.conjR hl)))
  apply intro_inputs
  intro j
  have hj : j = (0 : Fin 7) ∨ j = (1 : Fin 7) ∨ j = (2 : Fin 7) ∨ j = (3 : Fin 7) ∨ j = (4 : Fin 7) ∨ j = (5 : Fin 7) ∨ j = (6 : Fin 7) := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hr
  · exact hs
  · exact .conjL hc
  · exact .conjL hd
  · exact .conjR hc
  · exact .conjR hd
  · exact hq

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d q h : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (cell w r s a b c d q h)) : Derives Γ (.mem h w) :=
  SyntaxForests.range hZ 7 w (seven r s a b c d q) h hw hc

theorem field_natural {m} {Γ : Context m} (w r s a b c d q h : Fin m) (j : Fin 7)
    (hc : Derives Γ (cell w r s a b c d q h)) : Derives Γ (.mem (seven r s a b c d q j) w) :=
  SyntaxForests.input_at 7 w (seven r s a b c d q) h j hc

theorem same_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (cell w r s a b c d q h))
    (hd : Derives Γ (cell w r1 s1 a1 b1 c1 d1 q1 h)) :
    Derives Γ (.equal (seven r s a b c d q j) (seven r1 s1 a1 b1 c1 d1 q1 j)) :=
  SyntaxForestInjective.input_eq hZ 7 w _ _ h j hw hc hd

theorem same_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (cell w r s a b c d q h))
    (hd : Derives Γ (cell w r1 s1 a1 b1 c1 d1 q1 h)) :
    Derives Γ (equalParams r s a b c d q r1 s1 a1 b1 c1 d1 q1) := by
  have he (j : Fin 7) := same_field hZ w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j hw hc hd
  exact .conjI (he 0) (.conjI (he 1) (.conjI (he 2) (.conjI (he 3) (.conjI (he 4) (.conjI (he 5) (he 6))))))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d q h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (cell w r s a b c d q h)) (ht : Derives Γ (cell w r s a b c d q t)) :
    Derives Γ (.equal h t) := SyntaxForests.unique hZ 7 w (seven r s a b c d q) h t hw hh ht

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (legal w r s a b c d q)) : Derives Γ (stateFiber w r s a b c d q) := by
  have he := SyntaxForests.exists_forest hZ 7 w (seven r s a b c d q) hw (legal_inputs w r s a b c d q hl)
  let H := (Formula.mem (Fin.last m) w.castSucc).conj (cell w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ H
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw H
  have hl1 : Derives Ξ (legal w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc) := by simpa only [Formula.raise, legal_rename] using under hl H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((cell w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := cell w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add T (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 T
    have hh2 : Derives Δ (cell w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, cell_rename] using under (Derives.conjR hH) T
    exact unique (ZFContext.under hZ1 T) _ _ _ _ _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hh2
  have ho : Derives Ξ (stateFiber w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, cell_rename, state_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI (.conjL hH) (.conjI (.conjR hH) hl1)) hu
  simpa only [Formula.raise, stateFiber_rename] using ho
end PPAC.Migration.Internal.SyntaxRenameState
