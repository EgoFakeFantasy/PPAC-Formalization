import PPAC.Migration.Internal.SyntaxForestSyntax

/-! 固定有限向量的实际原森林构造、自然值域、唯一性及每个字段严格子码界。 -/
namespace PPAC.Migration.Internal.SyntaxForests
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax SyntaxForestSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest k w xs n)) : Derives Γ (.mem n w) := by
  cases k with
  | zero => exact StructuralNil.range hZ w n hw hn
  | succ k =>
    let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Δ := Context.add C (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hn
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact StructuralConsCore.range (ZFContext.under hZ C) _ _ _ _ hw1 (.conjR (.conjR hC))

theorem input_at {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hn : Derives Γ (forest k w xs n)) : Derives Γ (.mem (xs i) w) := by
  induction k generalizing m with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Δ := Context.add C (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hn
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .conjL hC
    · exact ih _ _ _ j (.conjL (.conjR hC))

theorem exists_forest {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputs k w xs)) : Derives Γ (existsForest k w xs) := by
  induction k generalizing m with
  | zero =>
    let U := unitWitness m
    let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
    apply StructuralListUnits.with_units w _ hw
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
    have hU : Derives Δ U := .hyp (Or.inl rfl)
    have hn := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
    have hc := StructuralNil.at_unit hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
    have hout := intro_exists 0 w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) _ hn hc
    simpa only [Formula.raise, existsForest_rename] using hout
  | succ k ih =>
    have ht := ih hZ w (fun i => xs i.succ) hw (.conjR hi)
    let T := (Formula.mem (Fin.last m) w.castSucc).conj (forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m))
    let Ξ := Context.add T (Context.image Formula.raise Γ)
    change Derives Γ (.ex T) at ht
    apply Derives.exE (p := T) ht
    have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ T
    have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
    have hh1 : Derives Ξ (.mem (xs 0).castSucc w.castSucc) := under (.conjL hi) T
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have hn := StructuralConsCore.exists_cons hZ1 _ _ _ hw1 hh1 (.conjL hT)
    let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Δ := Context.add N (Context.image Formula.raise Ξ)
    change Derives Ξ (.ex N) at hn
    apply Derives.exE (p := N) hn
    have hh2 : Derives Δ (.mem (xs 0).castSucc.castSucc w.castSucc.castSucc) := under hh1 N
    have hT2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
        (forest k w.castSucc.castSucc (fun i => (xs i.succ).castSucc.castSucc) (Fin.last m).castSucc)) := by
      simpa only [T, Formula.raise, Formula.rename, forest_rename] using under hT N
    have hN : Derives Δ N := .hyp (Or.inl rfl)
    have hc := SyntaxForestSyntax.intro_cons k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) _ _ hh2 (.conjR hT2) (.conjR hN)
    have hout := intro_exists (k+1) _ _ _ (.conjL hN) hc
    simpa only [Formula.raise, existsForest_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest k w xs n)) (hr : Derives Γ (forest k w xs r)) : Derives Γ (.equal n r) := by
  induction k generalizing m with
  | zero => exact StructuralNil.unique hZ w n r hw hn hr
  | succ k ih =>
    let N := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Ξ := Context.add N (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hn
    have hr1 : Derives Ξ (forest (k+1) w.castSucc (fun i => (xs i).castSucc) r.castSucc) := by simpa only [Formula.raise, forest_rename] using under hr N
    let R := (Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (xs i.succ).castSucc.castSucc) (Fin.last (m+1))).conj
        (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    apply eliminate_cons k w.castSucc (fun i => (xs i).castSucc) r.castSucc _ hr1
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
    have hN : Derives Ξ N := .hyp (Or.inl rfl)
    have hN2 : Derives Δ ((Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
        ((forest k w.castSucc.castSucc (fun i => (xs i.succ).castSucc.castSucc) (Fin.last m).castSucc).conj
          (consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
      simpa only [N, Formula.raise, Formula.rename, forest_rename, consCode_rename] using under hN R
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have heq := ih hZ2 _ _ _ _ hw2 (.conjL (.conjR hN2)) (.conjL (.conjR hR))
    have hcons := cons_tail_subst _ _ _ _ _ (eq_symm heq) (.conjR (.conjR hR))
    exact StructuralConsUnique.unique hZ2 _ _ _ _ _ hw2 (.conjL hN2) (range hZ2 _ _ _ _ hw2 (.conjL (.conjR hN2))) (.conjR (.conjR hN2)) hcons

theorem entry_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest k w xs n)) : Derives Γ (.mem (xs i) n) := by
  induction k generalizing m with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj (consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
    let Δ := Context.add C (Context.image Formula.raise Γ)
    apply eliminate_cons k w xs n _ hn
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ C
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have ht := range hZ1 _ _ _ _ hw1 (.conjL (.conjR hC))
    have hb := StructuralConsCore.components hZ1 _ _ _ _ hw1 (.conjL hC) ht (.conjR (.conjR hC))
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .conjL hb
    · have ha := ih hZ1 _ _ _ j hw1 (.conjL (.conjR hC))
      have hnW := StructuralConsCore.range hZ1 _ _ _ _ hw1 (.conjR (.conjR hC))
      have ho := NaturalOrderBasic.ordinal hZ1 _ _ hw1 hnW
      have hs := OrdinalTransitivity.subset_of_member _ _ (.conjL ho) (.conjR hb)
      exact .impE (RestrictionSyntax.subset_at _ _ _ hs) ha
end PPAC.Migration.Internal.SyntaxForests
