import PPAC.Migration.Internal.ObjectSyntaxCompose

/-! 提升复合的全部内部正向点：零边与同步后继边，中间后继由原Pairing/Union实际构造。 -/
namespace PPAC.Migration.Internal.SyntaxComposeLiftPoint
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxIndexLiftSyntax
open SyntaxComposeSyntax (composed composed_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e A C E ρ τ i j : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hi : Derives Γ (empty i)) (hj : Derives Γ (empty j)) : Derives Γ (SyntaxComposeSyntax.value ρ τ i j) := by
  have er := Derives.impE (.conjR (SyntaxIndexLift.edge_iff hZ w r a c A C ρ i i hw hr)) (.disjL (.conjI hi hi))
  have et := Derives.impE (.conjR (SyntaxIndexLift.edge_iff hZ w t c e C E τ i j hw ht)) (.disjL (.conjI hi hj))
  exact SyntaxComposeSyntax.intro_value ρ τ i j i er et

theorem shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ i j : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hv : Derives Γ (SyntaxIndexLiftSyntax.shifted g a i j)) : Derives Γ (SyntaxComposeSyntax.value ρ τ i j) := by
  let B := shiftBody g a i j
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_shifted g a i j _ hv
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hg2 : Derives Ξ (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc) := of_eq (by simp only [Formula.raise, composed_rename]) (SyntaxRenameBinders.under_2 hg B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hm := Derives.impE (.conjL (SyntaxComposeGraph.edge_iff hZ2 w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hg2)) (.conjR (.conjL hB))
  let D := (edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj (edge t.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc)
  let Ψ := Context.add D (Context.image Formula.raise Ξ)
  apply Derives.exE (p := D) hm
  have hZ3 := ZFContext.under hZ2 D
  have hg3 : Derives Ψ (composed w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := of_eq (composed_rename _ _ _ _ _ _ _ Fin.castSucc) (under hg2 D)
  have hD : Derives Ψ D := .hyp (Or.inl rfl)
  have hm3 := SyntaxIndexMapSyntax.edge_target w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (.conjL hg3) (.conjL hD)
  have hs := InsertExistence.exists_insert (Fin.last (m+2)) (Fin.last (m+2)) (ZFContext.arithmetic hZ3).base.pairing (ZFContext.arithmetic hZ3).base.union
  let S := successor (Fin.last (m+3)) (Fin.last (m+2)).castSucc
  let Δ := Context.add S (Context.image Formula.raise Ψ)
  apply Derives.exE (p := S) hs
  have hZ4 := ZFContext.under hZ3 S
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under (SyntaxRenameBinders.under_2 hw B) D) S)
  have hr4 : Derives Δ (lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc ρ.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (under (under (SyntaxRenameBinders.under_2 hr B) D) S)
  have ht4 : Derives Δ (lifted w.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc.castSucc τ.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, lifted_rename]) (under (under (SyntaxRenameBinders.under_2 ht B) D) S)
  have hk4 : Derives Δ (Formula.mem (Fin.last m).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under (.conjL (.conjL hB)) D) S)
  have hi4 : Derives Δ (successor i.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under (.conjL (.conjR hB)) D) S)
  have hj4 : Derives Δ (successor j.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under (.conjR (.conjR hB)) D) S)
  have hm4 : Derives Δ (Formula.mem (Fin.last (m+2)).castSucc c.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (hm3) S)
  have er4 : Derives Δ (edge r.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc) := of_eq (by simp only [Formula.raise, edge_rename]) (under (.conjL hD) S)
  have et4 : Derives Δ (edge t.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc) := of_eq (by simp only [Formula.raise, edge_rename]) (under (.conjR hD) S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have vr := intro_shifted r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hk4 er4 hi4 hS
  have vt := intro_shifted t.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) j.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc hm4 et4 hS hj4
  have er := Derives.impE (.conjR (SyntaxIndexLift.edge_iff hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc ρ.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) hw4 hr4)) (.disjR vr)
  have et := Derives.impE (.conjR (SyntaxIndexLift.edge_iff hZ4 w.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc.castSucc τ.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) j.castSucc.castSucc.castSucc.castSucc hw4 ht4)) (.disjR vt)
  have ho := SyntaxComposeSyntax.intro_value ρ.castSucc.castSucc.castSucc.castSucc τ.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) er et
  exact of_eq (by simp only [Formula.raise, SyntaxComposeSyntax.value_rename]) ho

theorem value_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ i j : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hv : Derives Γ (value g a i j)) : Derives Γ (SyntaxComposeSyntax.value ρ τ i j) := by
  apply Derives.disjE hv
  · have hV : Derives (Context.add ((empty i).conj (empty j)) Γ) ((empty i).conj (empty j)) := .hyp (Or.inl rfl)
    exact zero (ZFContext.add hZ _) w r t a c e A C E ρ τ i j (add hw _) (add hr _) (add ht _) (.conjL hV) (.conjR hV)
  · exact shifted (ZFContext.add hZ _) w r t a c e g A C E ρ τ i j (add hw _) (add hg _) (add hr _) (add ht _) (.hyp (Or.inl rfl))

theorem edge_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g A C E ρ τ γ i j : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (composed w r t a c e g))
    (hr : Derives Γ (lifted w r a c A C ρ)) (ht : Derives Γ (lifted w t c e C E τ))
    (hγ : Derives Γ (lifted w g a e A E γ)) (he : Derives Γ (edge γ i j)) : Derives Γ (SyntaxComposeSyntax.value ρ τ i j) :=
  value_forward hZ w r t a c e g A C E ρ τ i j hw hg hr ht (.impE (.conjL (SyntaxIndexLift.edge_iff hZ w g a e A E γ i j hw hγ)) he)
end PPAC.Migration.Internal.SyntaxComposeLiftPoint
