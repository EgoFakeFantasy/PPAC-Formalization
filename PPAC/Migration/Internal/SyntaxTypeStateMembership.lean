import PPAC.Migration.Internal.SyntaxTypeStateExistence

/-! 实际状态的逐对成员精确双条件；排除杂项、非法上下文和非自然输入。 -/
namespace PPAC.Migration.Internal.SyntaxTypeStateMembership
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax GraphSyntax GraphLogic PowerSetSyntax SyntaxTermSyntax SyntaxFormulaLocalSyntax SyntaxTypeStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem no_junk {m} {Γ : Context m} (w c n h v p : Fin m)
    (hs : Derives Γ (state w c n h v)) (hp : Derives Γ (.mem p v)) :
    Derives Γ ((Formula.mem p c).conj (row w n h p)) := .impE (.conjL (state_at w c n h v p hs)) hp

theorem local_of_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v b f : Fin m)
    (hs : Derives Γ (state w c n h v)) (he : Derives Γ (edge v b f)) : Derives Γ (localType w b f h n) := by
  let P := (Formula.mem (Fin.last m) v.castSucc).conj (ordered (Fin.last m) b.castSucc f.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply edge_elim v b f _ he
  have hs1 : Derives Δ (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using under hs P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hr := Derives.conjR (no_junk _ _ _ _ _ _ hs1 (.conjL hP))
  have hout := SyntaxTypeStateRows.at_pair (ZFContext.under hZ P) _ _ _ _ _ _ (.conjR hP) hr
  simpa only [Formula.raise, localType_rename] using hout

theorem edge_of_local {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n h v b f : Fin m)
    (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a)) (hs : Derives Γ (state w c n h v))
    (hl : Derives Γ (localType w b f h n)) : Derives Γ (edge v b f) := by
  have hctx := SyntaxFormulaLocal.context w b f h n hl
  have hp := SyntaxContextCarrier.pair_exists hZ w a c b f ha hc (.conjL hctx) (.conjR hctx)
  let P := (Formula.mem (Fin.last m) c.castSucc).conj (ordered (Fin.last m) b.castSucc f.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hp
  have hs1 : Derives Δ (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using under hs P
  have hl1 : Derives Δ (localType w.castSucc b.castSucc f.castSucc h.castSucc n.castSucc) := by
    simpa only [Formula.raise, localType_rename] using under hl P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hr := intro_row _ _ _ _ _ _ (.conjR hP) hl1
  have hm := Derives.impE (.conjR (state_at _ _ _ _ _ _ hs1)) (.conjI (.conjL hP) hr)
  have hout := edge_intro v.castSucc b.castSucc f.castSucc (Fin.last m) hm (.conjR hP)
  simpa only [Formula.raise, edge_rename] using hout

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n h v b f : Fin m)
    (ha : Derives Γ (powerOf a w)) (hc : Derives Γ (powerOf c a)) (hs : Derives Γ (state w c n h v)) :
    Derives Γ ((edge v b f).iff (localType w b f h n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact local_of_edge (ZFContext.add hZ _) w c n h v b f (add hs _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact edge_of_local (ZFContext.add hZ _) w a c n h v b f (add ha _) (add hc _) (add hs _) (.hyp (Or.inl rfl))

theorem bad_context {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v b f : Fin m)
    (hs : Derives Γ (state w c n h v)) (hb : Derives Γ (contexts w b f).neg) : Derives Γ (edge v b f).neg := by
  apply Derives.impI
  have hl := local_of_edge (ZFContext.add hZ (edge v b f)) w c n h v b f (add hs _) (.hyp (Or.inl rfl))
  exact .impE (add hb _) (SyntaxFormulaLocal.context w b f h n hl)

theorem row_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n h p)) : Derives Γ (.mem n w) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_row w n h p _ hr
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocal.range (ZFContext.under_two hZ B) _ _ _ _ _ hw2 (.conjR hB)

theorem member_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v p : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (state w c n h v)) (hp : Derives Γ (.mem p v)) : Derives Γ (.mem n w) :=
  row_natural hZ w n h p hw (.conjR (no_junk w c n h v p hs hp))

theorem off_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Formula.mem n w).neg) (hs : Derives Γ (state w c n h v)) : Derives Γ (empty v) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) v.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hs1 : Derives Δ (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using under hs M
  exact .impE (under hn M) (member_natural (ZFContext.under hZ M) _ _ _ _ _ _ hw1 hs1 (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.SyntaxTypeStateMembership
