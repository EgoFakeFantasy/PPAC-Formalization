import PPAC.Migration.Internal.SyntaxComposeLiftPoint

/-! 原完整同域函数图相等关闭提升复合的反向边，取得所有候选上的完整Composed。 -/
namespace PPAC.Migration.Internal.SyntaxComposeLiftGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax GraphPointwiseSyntax SyntaxRenameQuerySyntax
open SyntaxComposeSyntax
open SyntaxIndexLiftSyntax (lifted lifted_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem agrees_of_included {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f g d : Fin m)
    (hg : Derives Γ (functionOn g d)) (hi : Derives Γ (edgeIncluded f g)) : Derives Γ (GraphFamilySyntax.agrees f g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Ξ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hg3 : Derives Ξ (functionOn g.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (by simp only [functionOn_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)))
  have hi3 : Derives Ξ (edgeIncluded f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := of_eq (by simp only [edgeIncluded_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hi)))
  apply Derives.impI
  apply Derives.impI
  let P := edge f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
  let Q := edge g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add Q (Context.add P Ξ)
  have hZ3 := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) P) Q
  have hf : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have hy := Derives.impE (edgeIncluded_at _ _ _ _ (add (add hi3 P) Q)) hf
  exact GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (add (add hg3 P) Q) hy (.hyp (Or.inl rfl))

theorem included {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ k : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) (hk : Derives Γ (composed w ρ τ A C E k)) : Derives Γ (edgeIncluded γ k) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := edge γ.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hg2 : Derives Δ (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (SyntaxRenameBinders.under_2 hg B)
  have hr2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc ρ.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 hr B)
  have ht2 : Derives Δ (lifted w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc C.castSucc.castSucc E.castSucc.castSucc τ.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 ht B)
  have hγ2 : Derives Δ (lifted w.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc e.castSucc.castSucc A.castSucc.castSucc E.castSucc.castSucc γ.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (SyntaxRenameBinders.under_2 hγ B)
  have hk2 : Derives Δ (composed w.castSucc.castSucc ρ.castSucc.castSucc τ.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc E.castSucc.castSucc k.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (SyntaxRenameBinders.under_2 hk B)
  have hv := SyntaxComposeLiftPoint.edge_forward hZ2 w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc E.castSucc.castSucc ρ.castSucc.castSucc τ.castSucc.castSucc γ.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hg2 hr2 ht2 hγ2 (Derives.hyp (Or.inl rfl) : Derives Δ B)
  exact .impE (.conjR (SyntaxComposeGraph.edge_iff hZ2 _ _ _ _ _ _ _ _ _ hk2)) hv

theorem equal_to_composite {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ k : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) (hk : Derives Γ (composed w ρ τ A C E k)) : Derives Γ (.equal γ k) := by
  have ff := Derives.conjL (.conjR (SyntaxIndexLift.target_map _ _ _ _ _ _ _ hγ))
  have fk := Derives.conjL (.conjR (SyntaxComposeGraph.target_map _ _ _ _ _ _ _ hk))
  have ha := agrees_of_included hZ γ k A fk (included hZ w r t a c e g A C E ρ τ γ k hw hg hr ht hγ hk)
  exact GraphPointwise.equal_of_agrees γ k A (ZFContext.arithmetic hZ).base.extensionality ff fk ha

theorem composition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) : Derives Γ (composed w ρ τ A C E γ) := by
  let B := composed w.castSucc ρ.castSucc τ.castSucc A.castSucc C.castSucc E.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxComposeGraph.exists_graph hZ w ρ τ A C E (SyntaxIndexLift.target_map _ _ _ _ _ _ _ hr) (SyntaxIndexLift.target_map _ _ _ _ _ _ _ ht))
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw B)
  have hg1 : Derives Δ (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under hg B)
  have hr1 : Derives Δ (lifted w.castSucc r.castSucc a.castSucc c.castSucc A.castSucc C.castSucc ρ.castSucc) := of_eq (lifted_rename _ _ _ _ _ _ _ Fin.castSucc) (under hr B)
  have ht1 : Derives Δ (lifted w.castSucc t.castSucc c.castSucc e.castSucc C.castSucc E.castSucc τ.castSucc) := of_eq (lifted_rename _ _ _ _ _ _ _ Fin.castSucc) (under ht B)
  have hγ1 : Derives Δ (lifted w.castSucc g.castSucc a.castSucc e.castSucc A.castSucc E.castSucc γ.castSucc) := of_eq (lifted_rename _ _ _ _ _ _ _ Fin.castSucc) (under hγ B)
  have he := equal_to_composite hZ1 w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc A.castSucc C.castSucc E.castSucc ρ.castSucc τ.castSucc γ.castSucc (Fin.last m) hw1 hg1 hr1 ht1 hγ1 (.hyp (Or.inl rfl))
  exact of_eq (composed_rename w ρ τ A C E γ Fin.castSucc).symm (SyntaxComposeCodeSyntax.subst_output _ _ _ _ _ _ _ _ (eq_symm he) (.hyp (Or.inl rfl)))

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ i j : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) : Derives Γ ((edge γ i j).iff (value ρ τ i j)) :=
  SyntaxComposeGraph.edge_iff hZ w ρ τ A C E γ i j (composition hZ w r t a c e g A C E ρ τ γ hw hg hr ht hγ)

theorem value_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ i j : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) : Derives Γ ((SyntaxIndexLiftSyntax.value g a i j).iff (value ρ τ i j)) := by
  have h1 := SyntaxIndexLift.edge_iff hZ w g a e A E γ i j hw hγ
  have h2 := edge_iff hZ w r t a c e g A C E ρ τ γ i j hw hg hr ht hγ
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL h2) _) (.impE (add (.conjR h1) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjL h1) _) (.impE (add (.conjR h2) _) (.hyp (Or.inl rfl)))
theorem lift_output_subst {m} {Γ : Context m} (w g a e A E γ k : Fin m)
    (he : Derives Γ (.equal γ k)) (hγ : Derives Γ (lifted w g a e A E γ)) : Derives Γ (lifted w g a e A E k) := by
  let P := lifted w.castSucc g.castSucc a.castSucc e.castSucc A.castSucc E.castSucc (Fin.last m)
  have e0 : P.instantiate γ = lifted w g a e A E γ := by simp only [P, Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate k = lifted w g a e A E k := by simp only [P, Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hγ))

theorem lifted_iff_composed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ)) :
    Derives Γ ((lifted w g a e A E γ).iff (composed w ρ τ A C E γ)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact composition (ZFContext.add hZ _) w r t a c e g A C E ρ τ γ (add hw _) (add hg _) (add hr _) (add ht _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let X := composed w ρ τ A C E γ
    have he := SyntaxIndexLift.exists_lift (ZFContext.add hZ X) w g a e A E (add hw X) (add (SyntaxComposeGraph.target_map _ _ _ _ _ _ _ hg) X)
      (add (.conjL (.conjR hr)) X) (add (.conjL (.conjR (.conjR ht))) X)
    let B := lifted w.castSucc g.castSucc a.castSucc e.castSucc A.castSucc E.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add X Γ))
    apply Derives.exE (p := B) he
    have hZ1 := ZFContext.under (ZFContext.add hZ X) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under (add hw X) B)
    have hg1 : Derives Δ (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add hg X) B)
    have hr1 : Derives Δ (lifted w.castSucc r.castSucc a.castSucc c.castSucc A.castSucc C.castSucc ρ.castSucc) := of_eq (lifted_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add hr X) B)
    have ht1 : Derives Δ (lifted w.castSucc t.castSucc c.castSucc e.castSucc C.castSucc E.castSucc τ.castSucc) := of_eq (lifted_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add ht X) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hx1 : Derives Δ (composed w.castSucc ρ.castSucc τ.castSucc A.castSucc C.castSucc E.castSucc γ.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under (Derives.hyp (Or.inl rfl) : Derives (Context.add X Γ) X) B)
    have hc := composition hZ1 w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc g.castSucc A.castSucc C.castSucc E.castSucc ρ.castSucc τ.castSucc (Fin.last m) hw1 hg1 hr1 ht1 hB
    have hEq := SyntaxComposeGraph.unique hZ1 _ _ _ _ _ _ _ _ hc hx1
    exact of_eq (lifted_rename w g a e A E γ Fin.castSucc).symm (lift_output_subst _ _ _ _ _ _ _ _ hEq hB)
end PPAC.Migration.Internal.SyntaxComposeLiftGraph
