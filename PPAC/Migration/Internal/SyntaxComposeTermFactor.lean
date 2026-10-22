import PPAC.Migration.Internal.SyntaxComposeTerms

/-! 复合图上的项重命名精确等价于两阶段实际重命名；中间项码由对象存在量词取得。 -/
namespace PPAC.Migration.Internal.SyntaxComposeTermFactor
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxRenameQuerySyntax SyntaxComposeSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def sequential {m} (w r s t u a b c d e f n v : Fin m) : Formula m := .ex
  ((renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (renamed w.castSucc t.castSucc u.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) v.castSucc))

theorem sequential_rename {m k} (w r s t u a b c d e f n v : Fin m) (ρ : Fin m → Fin k) :
    (sequential w r s t u a b c d e f n v).rename ρ = sequential (ρ w) (ρ r) (ρ s) (ρ t) (ρ u) (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) (ρ n) (ρ v) := by
  simp only [sequential, Formula.rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_sequential {m} {Γ : Context m} (w r s t u a b c d e f n v q : Fin m)
    (hf : Derives Γ (renamed w r s a b c d n q)) (hs : Derives Γ (renamed w t u c d e f q v)) :
    Derives Γ (sequential w r s t u a b c d e f n v) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hf hs)

theorem factor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s t u g h a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g)) (hh : Derives Γ (composed w s u b d f h))
    (hc : Derives Γ (renamed w g h a b e f n v)) : Derives Γ (sequential w r s t u a b c d e f n v) := by
  have mf := Derives.conjI (.conjL hg) (.conjL hh)
  have ms := Derives.conjI (.conjL (.conjR hg)) (.conjL (.conjR hh))
  have he := SyntaxRenameTermExistence.for_term hZ w r s a b c d n hw mf (SyntaxRenameTermTyping.source_term _ _ _ _ _ _ _ _ _ hc)
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have ms1 : Derives Ξ (maps w.castSucc t.castSucc u.castSucc c.castSucc d.castSucc e.castSucc f.castSucc) := of_eq (maps_rename _ _ _ _ _ _ _ Fin.castSucc) (under ms Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have he2 := SyntaxRenameTermExistence.for_term hZ1 w.castSucc t.castSucc u.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) hw1 ms1 (SyntaxRenameTermTyping.target_term _ _ _ _ _ _ _ _ _ (.conjR hQ))
  let V := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (renamed w.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add V (Context.image Formula.raise Ξ)
  apply Derives.exE (p := V) he2
  have hZ2 := ZFContext.under hZ1 V
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 V)
  have hg2 : Derives Δ (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (under (under hg Q) V)
  have hh2 : Derives Δ (composed w.castSucc.castSucc s.castSucc.castSucc u.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (under (under hh Q) V)
  have hc2 : Derives Δ (renamed w.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, renamed_rename]) (under (under hc Q) V)
  have hq2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [Q, Formula.raise, Formula.rename, renamed_rename]) (under hQ V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hd := SyntaxComposeTerms.forward hZ2 w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hg2 hh2 (.conjR hq2) (.conjR hV)
  have heq := SyntaxRenameTermUnique.unique hZ2 w.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc hw2 hd hc2
  have hs := SyntaxRenameTermIdentity.output_subst w.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) v.castSucc.castSucc heq (.conjR hV)
  have ho := intro_sequential w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (.conjR hq2) hs
  exact of_eq (by simp only [Formula.raise, sequential_rename]) ho

theorem collapse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s t u g h a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g)) (hh : Derives Γ (composed w s u b d f h))
    (hc : Derives Γ (sequential w r s t u a b c d e f n v)) : Derives Γ (renamed w g h a b e f n v) := by
  let Q := (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj (renamed w.castSucc t.castSucc u.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hc
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hg1 : Derives Δ (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under hg Q)
  have hh1 : Derives Δ (composed w.castSucc s.castSucc u.castSucc b.castSucc d.castSucc f.castSucc h.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under hh Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxComposeTerms.forward hZ1 w.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc n.castSucc (Fin.last m) v.castSucc hw1 hg1 hh1 (.conjL hQ) (.conjR hQ)
  exact of_eq (renamed_rename w g h a b e f n v Fin.castSucc).symm ho

theorem compose_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s t u g h a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g)) (hh : Derives Γ (composed w s u b d f h)) :
    Derives Γ ((renamed w g h a b e f n v).iff (sequential w r s t u a b c d e f n v)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact factor (ZFContext.add hZ _) w r s t u g h a b c d e f n v (add hw _) (add hg _) (add hh _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact collapse (ZFContext.add hZ _) w r s t u g h a b c d e f n v (add hw _) (add hg _) (add hh _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxComposeTermFactor
