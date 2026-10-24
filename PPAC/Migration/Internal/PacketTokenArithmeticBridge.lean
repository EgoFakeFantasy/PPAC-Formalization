import PPAC.Migration.Internal.PacketTokenArithmeticSyntax

/-! Real affine entries and the original zero guard give the exact four-witness arithmetic recursion. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenSyntax PacketTokenAcceptedSyntax
open PacketAffineSyntax PacketAffineCore
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hq : Derives Γ (.mem q w)) (hn : Derives Γ (empty q).neg) :
    Derives Γ (.mem z q) := by
  apply Derives.disjE (GodelUnpairArithmetic.zero_below hZ w z q hw hz hq)
  · have he : Derives (Context.add (Formula.equal z q) Γ) (.equal z q) := .hyp (Or.inl rfl)
    exact .botE (.impE (add hn _) (NaturalMultiplicationLaws.empty_subst z q he (add hz _)))
  · exact .hyp (Or.inl rfl)

theorem small_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketTokenRootSyntax.smallCase w B V n t a).iff (PacketTokenArithmeticSyntax.smallCase w B C n t a)) :=
  FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (PacketTokenCanonicalEntry.affine_entry_iff hZ true w C V n t a hw hC hv)

theorem large_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hl : Derives Γ (PacketTokenRootSyntax.largeCase w B V n t a)) :
    Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a) := by
  let L := PacketTokenRootSyntax.largeBody w B V n t a
  let Δ := Context.add L (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 L _ hl
  have hZ5 := HornBinderRules.zf_body 5 hZ L
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw L)
  have hB5 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 5)) (HornBinderRules.under_body 5 hB L)
  have hC5 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 5)) (HornBinderRules.under_body 5 hC L)
  have hv5 := of_eq (PacketTraceCore.value_rename w V (old 5)) (HornBinderRules.under_body 5 hv L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hg := Derives.conjL (.conjR (.conjR hL))
  have hp := Derives.conjR (.conjR (.conjR hL))
  have h0 := Derives.impE (.conjL (PacketTokenCanonicalEntry.affine_entry_iff hZ5 false (old 5 w) (old 5 B) (old 5 V)
    (slot 5 0) (slot 5 1) (old 5 n) hw5 hB5 hv5)) (.conjL hp)
  have ht := Derives.impE (.conjL (PacketTokenCanonicalEntry.entry_iff 2 (old 5 w) (old 5 V) (slot 5 1) (old 5 t) (slot 5 2) hv5)) (.conjL (.conjR hp))
  have h1 := Derives.impE (.conjL (PacketTokenCanonicalEntry.affine_entry_iff hZ5 true (old 5 w) (old 5 C) (old 5 V)
    (slot 5 4) (slot 5 2) (old 5 a) hw5 hC5 hv5)) (.conjR (.conjR hp))
  have hq : Derives Δ (empty (slot 5 1)).neg := by
    apply Derives.impI
    exact .impE (empty_at (slot 5 1) (slot 5 3) (.hyp (Or.inl rfl))) (add (.conjL hg) _)
  exact of_eq (PacketTokenArithmeticSyntax.largeCase_rename w B C n t a (old 5)).symm
    (PacketTokenArithmeticSyntax.intro_large (old 5 w) (old 5 B) (old 5 C) (old 5 n) (old 5 t) (old 5 a)
      (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 4) h0 hq (.conjL (.conjR hL)) ht h1)

theorem large_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hm : Derives Γ (PacketTokenArithmeticSyntax.largeCase w B C n t a)) :
    Derives Γ (PacketTokenRootSyntax.largeCase w B V n t a) := by
  let M := PacketTokenArithmeticSyntax.largeBody w B C n t a
  let ΓM := Context.add M (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 M _ hm
  have hZ4 := HornBinderRules.zf_body 4 hZ M
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw M)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB M)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC M)
  have hv4 := of_eq (PacketTraceCore.value_rename w V (old 4)) (HornBinderRules.under_body 4 hv M)
  let Z := (Formula.mem (Fin.last (m+4)) (old 4 w).castSucc).conj (empty (Fin.last (m+4)))
  let Δ := Context.add Z (Context.image Formula.raise ΓM)
  apply Derives.exE (p := Z) (SyntaxNumerals.exists_numeral hZ4 0 (old 4 w) hw4)
  have hZ5 := ZFContext.under hZ4 Z
  have hw5 := of_eq (omega_rename (old 4 w) Fin.castSucc) (under hw4 Z)
  have hB5 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 (old 4 B) Fin.castSucc) (under hB4 Z)
  have hC5 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 (old 4 C) Fin.castSucc) (under hC4 Z)
  have hv5 := of_eq (PacketTraceCore.value_rename (old 4 w) (old 4 V) Fin.castSucc) (under hv4 Z)
  have hM : Derives ΓM M := .hyp (Or.inl rfl)
  have h0 := of_eq (affine_rename (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) Fin.castSucc) (under (.conjL hM) Z)
  have hq : Derives Δ (empty (slot 4 1).castSucc).neg :=
    of_eq (by simp only [Formula.raise,Formula.neg,Formula.rename,empty_rename]) (under (.conjL (.conjR hM)) Z)
  have hs := of_eq (NaturalAdditionSyntax.sum_rename (old 4 w) (slot 4 0) (old 4 B) (slot 4 3) Fin.castSucc)
    (under (.conjL (.conjR (.conjR hM))) Z)
  have ht := of_eq (accepted_rename (old 4 w) (slot 4 1) (old 4 t) (slot 4 2) Fin.castSucc)
    (under (.conjL (.conjR (.conjR (.conjR hM)))) Z)
  have h1 := of_eq (affine_rename (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a) Fin.castSucc)
    (under (.conjR (.conjR (.conjR (.conjR hM)))) Z)
  have hZV : Derives Δ Z := .hyp (Or.inl rfl)
  have hzq := zero_member hZ5 (old 4 w).castSucc (Fin.last (m+4)) (slot 4 1).castSucc hw5 (.conjR hZV)
    (tail_guard _ _ _ _ _ h0) hq
  have hp0 := Derives.impE (.conjR (PacketTokenCanonicalEntry.affine_entry_iff hZ5 false (old 4 w).castSucc (old 4 B).castSucc (old 4 V).castSucc
    (slot 4 0).castSucc (slot 4 1).castSucc (old 4 n).castSucc hw5 hB5 hv5)) h0
  have hpt := Derives.impE (.conjR (PacketTokenCanonicalEntry.entry_iff 2 (old 4 w).castSucc (old 4 V).castSucc
    (slot 4 1).castSucc (old 4 t).castSucc (slot 4 2).castSucc hv5)) ht
  have hp1 := Derives.impE (.conjR (PacketTokenCanonicalEntry.affine_entry_iff hZ5 true (old 4 w).castSucc (old 4 C).castSucc (old 4 V).castSucc
    (slot 4 3).castSucc (slot 4 2).castSucc (old 4 a).castSucc hw5 hC5 hv5)) h1
  have ho := PacketTokenRootSyntax.intro_large (old 4 w).castSucc (old 4 B).castSucc (old 4 V).castSucc
    (old 4 n).castSucc (old 4 t).castSucc (old 4 a).castSucc (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc
    (Fin.last (m+4)) (slot 4 3).castSucc (.conjR hZV) hs (.conjI hzq (digit_guard _ _ _ _ _ h0)) (.conjI hp0 (.conjI hpt hp1))
  exact of_eq (by simp only [Formula.raise,PacketTokenRootSyntax.largeCase_rename]) ho

theorem large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketTokenRootSyntax.largeCase w B V n t a).iff (PacketTokenArithmeticSyntax.largeCase w B C n t a)) := by
  apply Derives.conjI
  · exact .impI (large_forward (ZFContext.add hZ _) w B C V n t a (add hw _) (add hB _) (add hC _) (add hv _) (.hyp (Or.inl rfl)))
  · exact .impI (large_backward (ZFContext.add hZ _) w B C V n t a (add hw _) (add hB _) (add hC _) (add hv _) (.hyp (Or.inl rfl)))

theorem criterion_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketTokenRootSyntax.criterion w B V n t a).iff (PacketTokenArithmeticSyntax.criterion w B C n t a)) :=
  SyntaxTypeLocalTransfer.disj_congr (small_iff hZ w B C V n t a hw hC hv) (large_iff hZ w B C V n t a hw hB hC hv)

end PPAC.Migration.Internal.PacketTokenArithmeticBridge
