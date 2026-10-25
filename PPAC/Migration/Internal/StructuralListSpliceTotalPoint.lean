import PPAC.Migration.Internal.StructuralListSpliceTotalSyntax

/-! Actual Nil and Cons construct the complete all-candidate splice fiber from the smaller real tail-code fiber. -/
namespace PPAC.Migration.Internal.StructuralListSpliceTotalPoint
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSyntax StructuralListSpliceTotalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) : Derives Γ (fiber w n t) := by
  have hSplice := Derives.impE (.conjR (StructuralListSplice.nil_iff hZ w n t t hw hn)) (.conjI ht (.eqRefl t))
  have hu : Derives Γ (uniqueAt w n t t) := by
    apply Derives.allI
    apply Derives.impI
    let H := splice w.castSucc n.castSucc t.castSucc (Fin.last m)
    have hZ1 := ZFContext.under hZ H
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
    have hn1 := of_eq (StructuralListSyntax.nilCode_rename w n Fin.castSucc) (under hn H)
    have hEq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff hZ1 _ _ _ _ hw1 hn1)) (.hyp (Or.inl rfl)))
    exact eq_symm hEq
  exact intro_fiber w n t t (StructuralListValidity.range w t ht) hSplice hu

theorem unique_from_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n t u a b : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w)) (hu : Derives Γ (.mem u w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (ha : Derives Γ (StructuralListSyntax.consCode w h u a))
    (hi : Derives Γ (uniqueAt w x t u)) (hb : Derives Γ (splice w n t b)) : Derives Γ (.equal b a) := by
  let R := (splice w.castSucc x.castSucc t.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) b.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSplice.cons_forward hZ w h x n t b hw hh hx hc hb)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi1 := of_eq (uniqueAt_rename w x t u Fin.castSucc) (under hi R)
  have ha1 := of_eq (StructuralListSyntax.consCode_rename w h u a Fin.castSucc) (under ha R)
  have heq := unique_at _ _ _ _ _ hi1 (.conjL hR)
  have hCons := cons_tail _ _ _ _ _ heq (.conjR hR)
  exact StructuralConsUnique.unique hZ1 _ _ _ _ _ hw1 (under hh R) (under hu R) hCons ha1

theorem cons_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hf : Derives Γ (fiber w x t)) : Derives Γ (fiber w n t) := by
  let R := fiberBody w x t
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hU : Derives Δ (.mem (Fin.last m) w.castSucc) := .conjL (.conjL hR)
  let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ1 _ _ _ hw1 hh1 hU)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hh2 : Derives Ξ (.mem h.castSucc.castSucc w.castSucc.castSucc) := under hh1 S
  have hx2 : Derives Ξ (.mem x.castSucc.castSucc w.castSucc.castSucc) := under (under hx R) S
  have hU2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hU S
  have hc2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListSyntax.consCode_rename]) (under (under hc R) S)
  have hSmall := of_eq (splice_rename w.castSucc x.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR (.conjL hR)) S)
  have hUnique := of_eq (uniqueAt_rename w.castSucc x.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) S)
  have hRemaining := StructuralListSplice.intro_remaining _ _ _ _ _ _ hSmall (.conjR hS)
  have hSplice := StructuralListSplice.cons_backward hZ2 _ _ _ _ _ _ hw2 hh2 hc2 hRemaining
  have hAll : Derives Ξ (uniqueAt w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))) := by
    apply Derives.allI
    apply Derives.impI
    let C := splice w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2))
    let Ω := Context.add C (Context.image Formula.raise Ξ)
    have hZ3 := ZFContext.under hZ2 C
    have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 C)
    have hc3 := of_eq (StructuralListSyntax.consCode_rename w.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc Fin.castSucc) (under hc2 C)
    have ha3 := of_eq (StructuralListSyntax.consCode_rename w.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) Fin.castSucc) (under (.conjR hS) C)
    have hi3 := of_eq (uniqueAt_rename w.castSucc.castSucc x.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc Fin.castSucc) (under hUnique C)
    exact unique_from_tail hZ3 w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (under hh2 C) (under hx2 C) (under hU2 C) hc3 ha3 hi3 (.hyp (Or.inl rfl) : Derives Ω C)
  have hout := intro_fiber w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) (.conjL hS) hSplice hAll
  simpa only [Formula.raise,fiber_rename] using hout

end PPAC.Migration.Internal.StructuralListSpliceTotalPoint
