import PPAC.Migration.Internal.RawCodeProjectionCanonical
import PPAC.Migration.Internal.SyntaxConstructors

/-! 实际有限原森林／构造器的合法固定槽位读取；外部arity/slot仅索引对象定理模式。 -/
namespace PPAC.Migration.Internal.RawCodeFieldAtConstructor
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem iff_trans {m} {Γ : Context m} {p q r : Formula m} (hp : Derives Γ (p.iff q)) (hq : Derives Γ (q.iff r)) : Derives Γ (p.iff r) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hq) _) (.impE (add (.conjL hp) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hp) _) (.impE (add (.conjR hq) _) (.hyp (Or.inl rfl)))

theorem forest_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxForestSyntax.forest k w xs n)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((RawCodeGetSyntax.get w n i y).iff (.equal y (xs j))) := by
  induction k generalizing m with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hi
      let B := (Formula.mem (xs 0).castSucc w.castSucc).conj
        ((SyntaxForestSyntax.forest k w.castSucc (fun a => (xs a.succ).castSucc) (Fin.last m)).conj
          (StructuralListSyntax.consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
      let Δ := Context.add B (Context.image Formula.raise Γ)
      apply SyntaxForestSyntax.eliminate_cons k w xs n _ hn
      have hZ1 := ZFContext.under hZ B
      have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
      have hi1 : Derives Δ (empty i.castSucc) := by simpa only [Formula.raise, Fin.val_zero, SyntaxNumeralSyntax.numeral, empty_rename] using under hi B
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have ht := SyntaxForests.range hZ1 k _ _ _ hw1 (.conjL (.conjR hB))
      have hz := RawCodeGetLaws.zero_iff hZ1 w.castSucc n.castSucc i.castSucc y.castSucc hw1 hi1
      have hc := RawCodeProjectionCanonical.on_cons_iff hZ1 true w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc y.castSucc hw1 (.conjL hB) ht (.conjR (.conjR hB))
      have hout := iff_trans hz hc
      simpa only [Formula.raise, Formula.iff, Formula.rename, RawCodeGetSyntax.get_rename, if_true] using hout
    · intro hi
      let B := (Formula.mem (xs 0).castSucc w.castSucc).conj
        ((SyntaxForestSyntax.forest k w.castSucc (fun a => (xs a.succ).castSucc) (Fin.last m)).conj
          (StructuralListSyntax.consCode w.castSucc (xs 0).castSucc (Fin.last m) n.castSucc))
      let Δ := Context.add B (Context.image Formula.raise Γ)
      apply SyntaxForestSyntax.eliminate_cons k w xs n _ hn
      have hZ1 := ZFContext.under hZ B
      have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
      have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral (j.val+1) i.castSucc) := by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, Fin.val_succ] using under hi B
      let I := (SyntaxNumeralSyntax.numeral j.val (Fin.last (m+1))).conj (successor i.castSucc.castSucc (Fin.last (m+1)))
      let Ξ := Context.add I (Context.image Formula.raise Δ)
      apply SyntaxNumeralSyntax.eliminate_succ j.val i.castSucc _ hi1
      have hZ2 := ZFContext.under hZ1 I
      have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 I
      have hB : Derives Δ B := .hyp (Or.inl rfl)
      have hB2 : Derives Ξ ((Formula.mem (xs 0).castSucc.castSucc w.castSucc.castSucc).conj
        ((SyntaxForestSyntax.forest k w.castSucc.castSucc (fun a => (xs a.succ).castSucc.castSucc) (Fin.last m).castSucc).conj
          (StructuralListSyntax.consCode w.castSucc.castSucc (xs 0).castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
        simpa only [B, Formula.raise, Formula.rename, SyntaxForestSyntax.forest_rename, StructuralListSyntax.consCode_rename] using under hB I
      have hI : Derives Ξ I := .hyp (Or.inl rfl)
      have ht := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hB2))
      have hr := SyntaxNumerals.range hZ2 j.val w.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjL hI)
      have htail := RawCodeProjectionCanonical.value_cons hZ2 false _ _ _ _ hw2 (.conjL hB2) ht (.conjR (.conjR hB2))
      have hs := RawCodeGetLaws.successor_iff hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc y.castSucc.castSucc hw2 hr (.conjR hI) htail
      have htread := ih hZ2 w.castSucc.castSucc (fun a => (xs a.succ).castSucc.castSucc) (Fin.last m).castSucc j (Fin.last (m+1)) y.castSucc.castSucc hw2 (.conjL (.conjR hB2)) (.conjL hI)
      have hout := iff_trans hs htread
      simpa only [Formula.raise, Formula.iff, Formula.rename, RawCodeGetSyntax.get_rename] using hout

theorem node_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)
    (n : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.node k w tag xs n)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((RawCodeFieldSyntax.field w n i y).iff (.equal y (xs j))) := by
  let B := SyntaxNodeSyntax.nodeBody k w tag xs n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_node k w tag xs n _ hn
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i.castSucc) := by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using under hi B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ1 k _ _ _ hw1 (.conjL (.conjR hB))
  have hf := RawCodeField.on_raw_iff hZ1 w.castSucc tag.castSucc (Fin.last m) n.castSucc i.castSucc y.castSucc hw1 (.conjL hB) hp (.conjR (.conjR hB))
  have hg := forest_at hZ1 k w.castSucc (fun a => (xs a).castSucc) (Fin.last m) j i.castSucc y.castSucc hw1 (.conjL (.conjR hB)) hi1
  have hout := iff_trans hf hg
  simpa only [Formula.raise, Formula.iff, Formula.rename, RawCodeFieldSyntax.field_rename] using hout

theorem constructor_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((RawCodeFieldSyntax.field w n i y).iff (.equal y (xs j))) := by
  let B := SyntaxNodeSyntax.constructorBody k tag w xs n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor k tag w xs n _ hn
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i.castSucc) := by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using under hi B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := node_at hZ1 k w.castSucc (Fin.last m) (fun a => (xs a).castSucc) n.castSucc j i.castSucc y.castSucc hw1 (.conjR hB) hi1
  simpa only [Formula.raise, Formula.iff, Formula.rename, RawCodeFieldSyntax.field_rename] using hout

end PPAC.Migration.Internal.RawCodeFieldAtConstructor
