import PPAC.Migration.Internal.StructuralListSpliceAlgebraTransport

/-! Actual Cons inversion and reconstruction lift associativity from the genuine smaller prefix to its actual Cons. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraCons
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSyntax StructuralListSpliceAlgebraSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hi : Derives Γ (associative w x))
    (hAB : Derives Γ (splice w n B AB)) (hBC : Derives Γ (splice w B C BC)) (hO : Derives Γ (splice w AB C O)) :
    Derives Γ (splice w n BC O) := by
  let R := (splice w.castSucc x.castSucc B.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) AB.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSplice.cons_forward hZ w h x n B AB hw hh hx hc hAB)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hx1 : Derives Δ (.mem x.castSucc w.castSucc) := under hx R
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x n Fin.castSucc) (under hc R)
  have hO1 := of_eq (splice_rename w AB C O Fin.castSucc) (under hO R)
  have hU := StructuralListSpliceTotal.natural _ _ _ _ (.conjL hR)
  have hRem := StructuralListSplice.cons_forward hZ1 w.castSucc h.castSucc (Fin.last m) AB.castSucc C.castSucc O.castSucc hw1 hh1 hU (.conjR hR) hO1
  let S := (splice w.castSucc.castSucc (Fin.last m).castSucc C.castSucc.castSucc (Fin.last (m+1))).conj (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) O.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hRem
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hh2 : Derives Ξ (.mem h.castSucc.castSucc w.castSucc.castSucc) := under hh1 S
  have hi2 : Derives Ξ (associative w.castSucc.castSucc x.castSucc.castSucc) := of_eq (by simp only [Formula.raise,associative_rename]) (under (under hi R) S)
  have hXB := of_eq (splice_rename w.castSucc x.castSucc B.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hBC2 : Derives Ξ (splice w.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc BC.castSucc.castSucc) := of_eq (by simp only [Formula.raise,splice_rename]) (under (under hBC R) S)
  have hNorm := associate_at w.castSucc.castSucc x.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc BC.castSucc.castSucc (Fin.last (m+1)) hi2 hXB hBC2
  have hSmall := Derives.impE (.conjL hNorm) (.conjL hS)
  have hRemaining := StructuralListSplice.intro_remaining _ _ _ _ _ _ hSmall (.conjR hS)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc x.castSucc n.castSucc Fin.castSucc) (under hc1 S)
  have hout := StructuralListSplice.cons_backward hZ2 _ _ _ _ _ _ hw2 hh2 hc2 hRemaining
  simpa only [Formula.raise,splice_rename] using hout

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hi : Derives Γ (associative w x))
    (hAB : Derives Γ (splice w n B AB)) (hBC : Derives Γ (splice w B C BC)) (hO : Derives Γ (splice w n BC O)) :
    Derives Γ (splice w AB C O) := by
  let R := (splice w.castSucc x.castSucc B.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) AB.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSplice.cons_forward hZ w h x n B AB hw hh hx hc hAB)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hx1 : Derives Δ (.mem x.castSucc w.castSucc) := under hx R
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x n Fin.castSucc) (under hc R)
  have hO1 := of_eq (splice_rename w n BC O Fin.castSucc) (under hO R)
  have hRem := StructuralListSplice.cons_forward hZ1 w.castSucc h.castSucc x.castSucc n.castSucc BC.castSucc O.castSucc hw1 hh1 hx1 hc1 hO1
  let S := (splice w.castSucc.castSucc x.castSucc.castSucc BC.castSucc.castSucc (Fin.last (m+1))).conj (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) O.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hRem
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have hh2 : Derives Ξ (.mem h.castSucc.castSucc w.castSucc.castSucc) := under hh1 S
  have hi2 : Derives Ξ (associative w.castSucc.castSucc x.castSucc.castSucc) := of_eq (by simp only [Formula.raise,associative_rename]) (under (under hi R) S)
  have hXB := of_eq (splice_rename w.castSucc x.castSucc B.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hBC2 : Derives Ξ (splice w.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc BC.castSucc.castSucc) := of_eq (by simp only [Formula.raise,splice_rename]) (under (under hBC R) S)
  have hNorm := associate_at w.castSucc.castSucc x.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc BC.castSucc.castSucc (Fin.last (m+1)) hi2 hXB hBC2
  have hSmall := Derives.impE (.conjR hNorm) (.conjL hS)
  have hRemaining := StructuralListSplice.intro_remaining _ _ _ _ _ _ hSmall (.conjR hS)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc (Fin.last m) AB.castSucc Fin.castSucc) (under (.conjR hR) S)
  have hout := StructuralListSplice.cons_backward hZ2 _ _ _ _ _ _ hw2 hh2 hc2 hRemaining
  simpa only [Formula.raise,splice_rename] using hout

theorem associate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n B C AB BC O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hi : Derives Γ (associative w x))
    (hAB : Derives Γ (splice w n B AB)) (hBC : Derives Γ (splice w B C BC)) :
    Derives Γ ((splice w AB C O).iff (splice w n BC O)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hh _) (add hx _) (add hc _) (add hi _) (add hAB _) (add hBC _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hh _) (add hx _) (add hc _) (add hi _) (add hAB _) (add hBC _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListSpliceAlgebraCons
