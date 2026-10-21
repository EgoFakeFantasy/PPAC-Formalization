import PPAC.Migration.Internal.StructuralListSuffixMatch

/-! 实际取得下一偏移、旧后缀码、源head及新Cons码，完成内部后缀编码后继构造。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixStep
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListSyntax StructuralListSuffixSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l r s k : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hr : Derives Γ (.mem r w))
    (hs : Derives Γ (successor s r)) (hi : Derives Γ (property w f l r)) (hk : Derives Γ (.mem k w))
    (hq : Derives Γ (sum w s k l)) : Derives Γ (existsCode w f k s) := by
  have hkl := StructuralListPositionArithmetic.old_index hZ w r s k l hw hr hk hs hq
  have hj := Derives.impE (step_at w k (.conjL hw)) hk
  let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) k.castSucc)
  let Ξ1 := Context.add J (Context.image Formula.raise Γ)
  change Derives Γ (.ex J) at hj
  apply Derives.exE (p := J) hj
  have hZ1 : ZFContext.Evidence Ξ1 := ZFContext.under hZ J
  have hw1 : Derives Ξ1 (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw J
  have hs1 : Derives Ξ1 (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs J
  have hq1 : Derives Ξ1 (sum w.castSucc s.castSucc k.castSucc l.castSucc) := by simpa only [Formula.raise, sum_rename] using under hq J
  have hi1 : Derives Ξ1 (property w.castSucc f.castSucc l.castSucc r.castSucc) := by simpa only [Formula.raise, property_rename] using under hi J
  have hJ : Derives Ξ1 J := .hyp (Or.inl rfl)
  have hsum := StructuralListPositionArithmetic.swap_successors hZ1 _ _ _ _ _ _ hw1 (under hr J) (under hk J) hs1 (.conjR hJ) hq1
  have ht := code_at _ _ _ _ _ hi1 (.conjL hJ) hsum
  let T := coded w.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc (Fin.last (m+1))
  let Ξ2 := Context.add T (Context.image Formula.raise Ξ1)
  change Derives Ξ1 (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ2 : ZFContext.Evidence Ξ2 := ZFContext.under hZ1 T
  have hf2 : Derives Ξ2 (sequence f.castSucc.castSucc l.castSucc.castSucc w.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using under (under hf J) T
  have hh := SequenceLogic.value_at _ _ _ _ hf2 (under (under hkl J) T)
  let H := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (valueAt f.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Ξ3 := Context.add H (Context.image Formula.raise Ξ2)
  change Derives Ξ2 (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hZ3 : ZFContext.Evidence Ξ3 := ZFContext.under hZ2 H
  have hw3 : Derives Ξ3 (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw1 T) H
  have hT : Derives Ξ2 T := .hyp (Or.inl rfl)
  have hT3 : Derives Ξ3 (coded w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := by
    simpa only [T, Formula.raise, coded_rename] using under hT H
  have hH : Derives Ξ3 H := .hyp (Or.inl rfl)
  have hn := StructuralConsCore.exists_cons hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hw3 (.conjL hH) (.conjL (.conjL hT3))
  let N := (Formula.mem (Fin.last (m+3)) w.castSucc.castSucc.castSucc.castSucc).conj
    (consCode w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)))
  let Δ := Context.add N (Context.image Formula.raise Ξ3)
  change Derives Ξ3 (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hZ4 : ZFContext.Evidence Δ := ZFContext.under hZ3 N
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise.raise.raise := under (under (under (under ha J) T) H) N
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf4 : Derives Δ (sequence f.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  have hs4 : Derives Δ (successor s.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hJ4 : Derives Δ ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [J, Formula.raise, Formula.rename, successor_rename] using under (under (under hJ T) H) N
  have hT4 : Derives Δ (coded w.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, coded_rename] using under hT3 N
  have hH4 : Derives Δ ((Formula.mem (Fin.last (m+2)).castSucc w.castSucc.castSucc.castSucc.castSucc).conj
      (valueAt f.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc)) := by
    simpa only [H, Formula.raise, Formula.rename, valueAt_rename] using under hH N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hlen := StructuralListLengthConstruct.cons_length hZ4 _ _ _ _ _ _ hw4 (.conjL hH4) (.conjR hN) (.conjR (.conjL hT4)) hs4
  have halign := StructuralListSuffixMatch.aligned_cons hZ4 _ _ _ _ _ _ _ _ _ _ hw4 hf4 (lift hr) (lift hk) hs4 (.conjR hJ4)
    (.conjL hH4) (.conjL (.conjL hT4)) (.conjR hN) (.conjL (.conjR hH4)) (.conjR hT4)
  have hout := intro_code _ _ _ _ _ (.conjL hN) hlen halign
  simpa only [Formula.raise, existsCode_rename] using hout

theorem property_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l r s : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hr : Derives Γ (.mem r w))
    (hs : Derives Γ (successor s r)) (hi : Derives Γ (property w f l r)) : Derives Γ (property w f l s) := by
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let Q := sum w.castSucc s.castSucc (Fin.last m) l.castSucc
  let Δ := Context.add Q (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.under hZ M) Q
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise := add (under ha M) Q
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf1 : Derives Δ (sequence f.castSucc l.castSucc w.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hi1 : Derives Δ (property w.castSucc f.castSucc l.castSucc r.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  exact point hZ1 _ _ _ _ _ _ hw1 hf1 (lift hr) hs1 hi1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListSuffixStep
