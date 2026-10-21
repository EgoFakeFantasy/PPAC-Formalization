import PPAC.Migration.Internal.SequenceContext

/-! 每次追加实际取得唯一新序列，精确保留旧图为旧域限制，所有长度均为内部集合。 -/
namespace PPAC.Migration.Internal.SequenceAppend
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax SequenceSyntax GraphInsertElimination

theorem from_witness {m} {Γ : Context m} (g e p k f n y b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (sequence f n b)) (hy : Derives Γ (.mem y b))
    (hn : Derives Γ (Formula.mem n n).neg) (hk : Derives Γ (successor k n))
    (hg : Derives Γ (GraphInsertSyntax.witness g e p f n n y)) : Derives Γ (append g k f n y b) := by
  have hop := Derives.conjL hg
  have hdom := Derives.conjL (.conjR hg)
  have hins := Derives.conjL (.conjR (.conjR hg))
  have hfn := Derives.conjL (.conjR (.conjR (.conjR hg)))
  have hlaw := Derives.conjR (.conjR (.conjR (.conjR hg)))
  have hbounded := SequenceLogic.appended_bounded g f n y b (.conjR hf) hy hlaw
  have hseq : Derives Γ (sequence g e b) := .conjI hfn hbounded
  have heq := OmegaUniversal.successor_unique e k n he hdom hk
  have hseqK := subst_domain g e k b heq hseq
  have hrestrict := GraphInsertRestriction.old_restriction g f n p n y he (.conjL hf) hn hins hop
  exact .conjI hseqK (.conjI hlaw hrestrict)

theorem exists_append {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (k f n y b : Fin m)
    (hf : Derives Γ (sequence f n b)) (hy : Derives Γ (.mem y b)) (hk : Derives Γ (successor k n)) :
    Derives Γ (appendExists k f n y b) := by
  have hn := ObjectIrreflexivity.no_self_member n hA.foundation hA.pairing
  have hex := GraphInsertExistence.exists_extension f n n y hA.pairing hA.union hA.extensionality (.conjL hf) hn
  let W := witnesses f n n y
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate f n n y _ hex
  have hAW := SequenceContext.under_three hA W
  have hfW : Derives Ξ (sequence f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, sequence_rename] using under_three hf W
  have hyW : Derives Ξ (.mem y.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) := under_three hy W
  have hnW : Derives Ξ (Formula.mem n.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc).neg := under_three hn W
  have hkW : Derives Ξ (successor k.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under_three hk W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have ha := from_witness (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    k.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc
    y.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc hAW.extensionality hfW hyW hnW hkW hW
  have hout : Derives Ξ (appendExists k.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
      n.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    simp only [Formula.instantiate, append_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact ha
  simpa only [Formula.raise, appendExists_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (k f n y b : Fin m)
    (hf : Derives Γ (sequence f n b)) (hy : Derives Γ (.mem y b)) (hk : Derives Γ (successor k n)) :
    Derives Γ (appendUnique k f n y b) := by
  have hex := exists_append hA k f n y b hf hy hk
  let G := append (Fin.last m) k.castSucc f.castSucc n.castSucc y.castSucc b.castSucc
  let Γg := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hex
  apply Derives.exE (p := G) hex
  have hAG := SequenceContext.under hA G
  have hG : Derives Γg G := .hyp (Or.inl rfl)
  have hu : Derives Γg (.all ((append (Fin.last (m+1)) k.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    let Δ := Context.image Formula.raise Γg
    have hA' := SequenceContext.rename hAG Fin.castSucc
    have hG' : Derives Δ (append (Fin.last m).castSucc k.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc) := by
      simpa only [Formula.raise, G, append_rename] using Derives.rename Fin.castSucc hG
    apply Derives.impI
    exact SequenceLogic.append_unique (Fin.last (m+1)) (Fin.last m).castSucc k.castSucc.castSucc
      f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc
      (add hA'.extensionality _) (.hyp (Or.inl rfl)) (add hG' _)
  have hout : Derives Γg (appendUnique k.castSucc f.castSucc n.castSucc y.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, append_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hG hu
  simpa only [Formula.raise, appendUnique_rename] using hout

theorem step_from_exists {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (n k y b : Fin m)
    (hn : Derives Γ (existsSequence n b)) (hy : Derives Γ (.mem y b)) (hk : Derives Γ (successor k n)) :
    Derives Γ (existsSequence k b) := by
  let F := sequence (Fin.last m) n.castSucc b.castSucc
  let Γf := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hn
  apply Derives.exE (p := F) hn
  have hAF := SequenceContext.under hA F
  have hyF : Derives Γf (.mem y.castSucc b.castSucc) := under hy F
  have hkF : Derives Γf (successor k.castSucc n.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hk F
  have hF : Derives Γf F := .hyp (Or.inl rfl)
  have hg := exists_append hAF k.castSucc (Fin.last m) n.castSucc y.castSucc b.castSucc hF hyF hkF
  let G := append (Fin.last (m+1)) k.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γf)
  change Derives Γf (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hout := intro_exists (Fin.last (m+1)) k.castSucc.castSucc b.castSucc.castSucc (.conjL hG)
  simpa only [Formula.raise, existsSequence_rename] using hout
end PPAC.Migration.Internal.SequenceAppend
