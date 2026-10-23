import PPAC.Migration.Internal.ArgumentForestProgramSyntax

/-! 精确有限森林与原全内部有类型列表在实际数码长度处的双向对应。 -/
namespace PPAC.Migration.Internal.ArgumentForestTyping
open Source SourceAlgebra SourceLogic OmegaSyntax ArgumentForestProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxForestSyntax SyntaxNumeralSyntax

theorem list_of_forest {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w l a b n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hf : Derives Γ (forest k w xs n)) (ht : Derives Γ (typedInputs k w a b xs)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w l a b n) := by
  have hFields : Derives Γ (SyntaxMixedImageCodeSyntax.typedFields w l a b n) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let A := (Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).conj
      (StructuralListFieldSyntax.field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 := ZFContext.under_two hZ A
    have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two h A
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
    have hl2 : Derives Δ (numeral k l.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (lift hl)
    have hf2 : Derives Δ (forest k w.castSucc.castSucc (fun j => (xs j).castSucc.castSucc) n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, forest_rename]) (lift hf)
    have ht2 : Derives Δ (typedInputs k w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (fun j => (xs j).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, typedInputs_rename]) (lift ht)
    have hA : Derives Δ A := .hyp (Or.inl rfl)
    have hb := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ2 k l.castSucc.castSucc (Fin.last m).castSucc hl2)) (.conjL hA)
    have hi : Derives Δ ((SyntaxPositionSyntax.below k (Fin.last m).castSucc).imp (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)))) := by
      apply SyntaxPositionSyntax.below_imp
      intro j
      apply Derives.impI
      let J := numeral j.val (Fin.last m).castSucc
      have hJ : Derives (Context.add J Δ) J := .hyp (Or.inl rfl)
      have he := Derives.impE (.conjL (SyntaxForestFieldValues.field_at (ZFContext.add hZ2 J) k w.castSucc.castSucc (fun t => (xs t).castSucc.castSucc) n.castSucc.castSucc j (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 J) (add hf2 J) hJ)) (add (.conjR hA) J)
      exact TypedArgumentListConstruction.term_output_subst _ _ _ _ _ (eq_symm he) (add (typed_at k _ _ _ _ ht2 j) J)
    exact .impE hi hb
  exact .conjI (SyntaxNumerals.range hZ k w l hw hl) (.conjI hc (.conjI
    (.conjI (SyntaxForests.range hZ k w xs n hw hf) (SyntaxForestLength.at_numeral hZ k w xs n l hw hf hl)) hFields))

theorem typed_of_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w l a b n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hf : Derives Γ (forest k w xs n))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w l a b n)) : Derives Γ (typedInputs k w a b xs) := by
  apply intro_typed
  intro j
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (numeral j.val (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ j.val w hw)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hl1 : Derives Δ (numeral k l.castSucc) := of_eq (numeral_rename k l Fin.castSucc) (under hl B)
  have hf1 : Derives Δ (forest k w.castSucc (fun t => (xs t).castSucc) n.castSucc) := of_eq (forest_rename k w xs n Fin.castSucc) (under hf B)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc l.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w l a b n Fin.castSucc) (under hL B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hIndex := SyntaxNumeralMembers.index_member hZ1 k j l.castSucc (Fin.last m) hl1 (.conjR hB)
  have hField := Derives.impE (.conjR (SyntaxForestFieldValues.field_at hZ1 k w.castSucc (fun t => (xs t).castSucc) n.castSucc j (Fin.last m) (xs j).castSucc hw1 hf1 (.conjR hB))) (.eqRefl _)
  have ho := SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hL1 hIndex hField
  exact of_eq (SyntaxTermSyntax.term_rename w a b (xs j) Fin.castSucc).symm ho

theorem list_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w l a b n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hc : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hf : Derives Γ (forest k w xs n)) :
    Derives Γ ((SyntaxMixedImageCodeSyntax.termList w l a b n).iff (typedInputs k w a b xs)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact typed_of_list (ZFContext.add hZ _) k w l a b n xs (add hw _) (add hl _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact list_of_forest (ZFContext.add hZ _) k w l a b n xs (add hw _) (add hl _) (add hc _) (add hf _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ArgumentForestTyping
