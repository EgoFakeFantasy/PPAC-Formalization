import PPAC.Migration.Internal.ProofTreeConstructorFacts

/-! 原根守卫var0<literal1的内部零界语义；不是把原literal1误当等号右值。 -/
namespace PPAC.Migration.Internal.ProofTreeZeroGuard
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem one_nonempty {m} {Γ : Context m} (x : Fin m) (hx : Derives Γ (SyntaxNumeralSyntax.numeral 1 x)) :
    Derives Γ (empty x).neg := by
  let B := (empty (Fin.last m)).conj (successor x.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ 0 x _ hx
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := InsertLogic.new_member x.castSucc (Fin.last m) (Fin.last m) (.conjR hB)
  have ho : Derives Δ (empty x.castSucc).neg := by
    apply Derives.impI
    exact .impE (empty_at x.castSucc (Fin.last m) (.hyp (Or.inl rfl))) (add hm _)
  exact of_eq (by simp only [Formula.raise, Formula.neg, Formula.rename, empty_rename]) ho

theorem one_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (u x : Fin m)
    (hx : Derives Γ (SyntaxNumeralSyntax.numeral 1 x)) : Derives Γ ((Formula.mem u x).iff (empty u)) := by
  let B := (empty (Fin.last m)).conj (successor x.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ 0 x _ hx
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have ho : Derives Δ ((Formula.mem u.castSucc x.castSucc).iff (empty u.castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      have hc := InsertLogic.member_cases x.castSucc (Fin.last m) (Fin.last m) u.castSucc (add (.conjR hB) _) (.hyp (Or.inl rfl))
      apply Derives.disjE hc
      · exact .botE (.impE (add (add (empty_at (Fin.last m) u.castSucc (.conjL hB)) _) _) (.hyp (Or.inl rfl)))
      · exact NaturalMultiplicationLaws.empty_subst (Fin.last m) u.castSucc (eq_symm (.hyp (Or.inl rfl))) (add (add (.conjL hB) _) _)
    · apply Derives.impI
      have he := OmegaUniversal.empty_unique (Fin.last m) u.castSucc (ZFContext.arithmetic (ZFContext.add hZ1 _)).base.extensionality (add (.conjL hB) _) (.hyp (Or.inl rfl))
      exact mem_subst he (add (InsertLogic.new_member x.castSucc (Fin.last m) (Fin.last m) (.conjR hB)) _)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, empty_rename]) ho

theorem guard_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i : Fin a) (w : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((HornRuleSyntax.guard (.var i) (.literal 1) w env).iff (empty (env i))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornRuleSyntax.guard (.var i) (.literal 1) w env
    let B := (graph (.var i) w.castSucc.castSucc (fun j => (env j).castSucc.castSucc) (Fin.last m).castSucc).conj
      ((SyntaxNumeralSyntax.numeral 1 (Fin.last (m+1))).conj (.mem (Fin.last m).castSucc (Fin.last (m+1))))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    apply SyntaxRenameBinders.eliminate_2 B _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hm := mem_subst (.conjR (.conjL hB)) (.conjR (.conjR hB))
    have ho := Derives.impE (.conjL (one_member_iff (SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ E) B) (env i).castSucc.castSucc (Fin.last (m+1)) (.conjL (.conjR hB)))) hm
    exact of_eq (by simp only [Formula.raise, empty_rename]) ho
  · apply Derives.impI
    let E := empty (env i)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral (ZFContext.add hZ E) 1 w (add hw E))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (under (add hn E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he : Derives Δ (empty (env i).castSucc) := of_eq (empty_rename (env i) Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hm := Derives.impE (.conjR (one_member_iff (ZFContext.under (ZFContext.add hZ E) B) (env i).castSucc (Fin.last m) (.conjR hB))) he
    have ho : Derives Δ (HornRuleSyntax.guard (.var i) (.literal 1) w.castSucc (fun j => (env j).castSucc)) := by
      apply Derives.exI (env i).castSucc
      apply Derives.exI (Fin.last m)
      simpa only [HornRuleSyntax.guard, graph, Formula.instantiate, Formula.rename, graph_rename, SyntaxNumeralSyntax.numeral_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using
        (Derives.conjI (Derives.conjI (environmentNat_at _ _ hn1 i) (Derives.eqRefl (env i).castSucc)) (Derives.conjI (Derives.conjR hB) hm))
    exact of_eq (HornRuleSyntax.guard_rename (.var i) (.literal 1) w env Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofTreeZeroGuard
