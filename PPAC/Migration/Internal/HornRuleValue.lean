import PPAC.Migration.Internal.HornRuleSyntax

/-! 上游单个真实前提与比较守卫的纯对象编译在实际内部值处精确。 -/
namespace PPAC.Migration.Internal.HornRuleValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornRuleSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem premise_at {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w trace y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hy : Derives Γ (graph e w env y)) :
    Derives Γ ((premise e w trace env).iff (.mem y trace)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := premise e w trace env
    let R := (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) trace.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp E) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (lift hn)
    have hy1 := of_eq (graph_rename e w y env Fin.castSucc) (lift hy)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have he := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) R) e _ _ _ _ hw1 hn1 (.conjL hR) hy1
    exact mem_subst he (.conjR hR)
  · apply Derives.impI
    apply Derives.exI y
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (add hy _) (.hyp (Or.inl rfl)))

theorem guard_at {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e f : Expr n) (w a b : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (ha : Derives Γ (graph e w env a)) (hb : Derives Γ (graph f w env b)) :
    Derives Γ ((guard e f w env).iff (.mem a b)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := guard e f w env
    let R := (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj
      ((graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj (.mem (Fin.last m).castSucc (Fin.last (m+1))))
    let Δ := Context.add R (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    apply SyntaxRenameBinders.eliminate_2 R _ (.hyp (Or.inl rfl))
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := SyntaxRenameBinders.under_2 (add hp E) R
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
    have hn2 : Derives Δ (environmentNat n w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hn)
    have ha2 : Derives Δ (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (lift ha)
    have hb2 : Derives Δ (graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (lift hb)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ E) R
    have hea := HornExprUnique.unique hZ2 e _ _ _ _ hw2 hn2 (.conjL hR) ha2
    have heb := HornExprUnique.unique hZ2 f _ _ _ _ hw2 hn2 (.conjL (.conjR hR)) hb2
    exact UnorderedPairLogic.mem_container_subst _ _ _ heb (mem_subst hea (.conjR (.conjR hR)))
  · apply Derives.impI
    apply Derives.exI a
    apply Derives.exI b
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (add ha _) (.conjI (add hb _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.HornRuleValue
