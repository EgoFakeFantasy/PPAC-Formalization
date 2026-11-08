import PPAC.Migration.ForcingCodeUnique
import PPAC.Migration.ForcingMixedBinary
import PPAC.Migration.SchemaClosureTyping
import PPAC.Migration.Internal.SyntaxVariableTableFields
import PPAC.Migration.Internal.SyntaxMixedImageCodePairs
import PPAC.Migration.Internal.SyntaxMixedFormulaOutputInduction

/-! Concrete code production for arbitrary open native proof formulas. Existing
mixed substitution sends fvar i to bvar i; the existing internal forall block
then closes all name slots before the actual forcing-code compiler is called.
R/H and the target parameter slots retain their existing contracts. All tables,
codes and closures are object witnesses, including at nonstandard scopes.
This is the code-production adapter; six-rule preservation and Con are not
claimed by its totality or uniqueness certificates. -/
namespace PPAC.Migration.ForcingOpenCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def reifyData {m} (w z b n t : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (SyntaxVariableTableSyntax.identity false w b z (v 0)).conj
    ((SyntaxVariableTableSyntax.identity true w b z (v 1)).conj
      ((SyntaxMixedImageCodeSyntax.encodings w (v 0) (v 1) z b b z (v 2) (v 3)).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 2) (v 3) z b b z n t)))
private theorem reifyData_rename {m l} (w z b n t : Fin m) (v : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (reifyData w z b n t v).rename r = reifyData (r w) (r z) (r b) (r n) (r t) (fun i => r (v i)) := by
  simp only [reifyData, Formula.rename, SyntaxVariableTableSyntax.identity_rename, SyntaxMixedImageCodeSyntax.encodings_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename]
private def reifyBody {m} (w z b n t : Fin m) : Formula (m+4) :=
  reifyData (old 4 w) (old 4 z) (old 4 b) (old 4 n) (old 4 t) (slot 4)

/-- On empty z, this replaces every free name by its bound variable, preserving
all binders through the existing mixed-substitution lifting laws. -/
def reified {m} (w z b n t : Fin m) : Formula m :=
  (formulaCode w n z b).conj (existsMany 4 (reifyBody w z b n t))
theorem reified_rename {m l} (w z b n t : Fin m) (r : Fin m → Fin l) :
    (reified w z b n t).rename r = reified (r w) (r z) (r b) (r n) (r t) := by
  simp only [reified, Formula.rename, formulaCode_rename, existsMany_rename, reifyBody, reifyData_rename, lift_old, lift_slot]

def existsReified {m} (w z b n : Fin m) : Formula m := .ex
  (reified w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m))
theorem existsReified_rename {m l} (w z b n : Fin m) (r : Fin m → Fin l) :
    (existsReified w z b n).rename r = existsReified (r w) (r z) (r b) (r n) := by
  simp only [existsReified, Formula.rename, reified_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_reified {m} {Γ : Context m} (w z b n t : Fin m) (v : Fin 4 → Fin m)
    (hc : Derives Γ (formulaCode w n z b)) (hd : Derives Γ (reifyData w z b n t v)) : Derives Γ (reified w z b n t) := by
  apply Derives.conjI hc
  apply HornBinderRules.intro_many 4 _ v
  exact of_eq (by simp only [reifyBody, reifyData_rename, assign_old, assign_slot]) hd

theorem reified_type {m} {Γ : Context m} (w z b n t : Fin m)
    (hr : Derives Γ (reified w z b n t)) : Derives Γ (formulaCode w t b z) := by
  let T := reifyBody w z b n t
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ (.conjR hr)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w t b z (old 4)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 4 w) (slot 4 2) (slot 4 3) (old 4 z) (old 4 b) (old 4 b) (old 4 z) (old 4 n) (old 4 t)
      (.conjR (.conjR (.conjR hT))))

private theorem from_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n r s L S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n z b))
    (hr : Derives Γ (SyntaxVariableTableSyntax.identity false w b z r))
    (hs : Derives Γ (SyntaxVariableTableSyntax.identity true w b z s))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s z b b z L S)) : Derives Γ (existsReified w z b n) := by
  let T := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L.castSucc S.castSucc z.castSucc b.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S z b b z n hw
    (.conjI hc (SyntaxMixedImageCodePairs.term_lists w r s z b b z L S he)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hc1 := of_eq (formulaCode_rename w n z b Fin.castSucc) (under hc T)
  have hr1 := of_eq (SyntaxVariableTableSyntax.identity_rename false w b z r Fin.castSucc) (under hr T)
  have hs1 := of_eq (SyntaxVariableTableSyntax.identity_rename true w b z s Fin.castSucc) (under hs T)
  have he1 := of_eq (SyntaxMixedImageCodeSyntax.encodings_rename w r s z b b z L S Fin.castSucc) (under he T)
  let v : Fin 4 → Fin (m+1) := Fin.cases r.castSucc (Fin.cases s.castSucc (SyntaxAtomSyntax.two L.castSucc S.castSucc))
  have hq := intro_reified w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m) v hc1 (.conjI hr1 (.conjI hs1 (.conjI he1 hT)))
  have ho : Derives Δ (existsReified w.castSucc z.castSucc b.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, reified_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsReified_rename w z b n Fin.castSucc).symm ho

private theorem from_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n r s : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n z b))
    (hr : Derives Γ (SyntaxVariableTableSyntax.identity false w b z r))
    (hs : Derives Γ (SyntaxVariableTableSyntax.identity true w b z s)) : Derives Γ (existsReified w z b n) := by
  let T := SyntaxMixedImageCodeSyntax.encodings (old 2 w) (old 2 r) (old 2 s) (old 2 z) (old 2 b) (old 2 b) (old 2 z) (slot 2 0) (slot 2 1)
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ (SyntaxMixedImageCodePairs.exists_codes hZ w r s z b b z hw
    (.conjI (SyntaxVariableTableUnique.identity_type false w b z r hr) (SyntaxVariableTableUnique.identity_type true w b z s hs)))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  apply of_eq (existsReified_rename w z b n (old 2)).symm
  exact from_environment (HornBinderRules.zf_body 2 hZ T) (old 2 w) (old 2 z) (old 2 b) (old 2 n) (old 2 r) (old 2 s) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (formulaCode_rename w n z b (old 2)) (HornBinderRules.under_body 2 hc T))
    (of_eq (SyntaxVariableTableSyntax.identity_rename false w b z r (old 2)) (HornBinderRules.under_body 2 hr T))
    (of_eq (SyntaxVariableTableSyntax.identity_rename true w b z s (old 2)) (HornBinderRules.under_body 2 hs T)) hT

/-- Actual complete tables, codes and substitution output, with no environment
or renamed formula supplied by the caller. -/
theorem reify_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n z b)) : Derives Γ (existsReified w z b n) := by
  have hg := Derives.conjR (FormulaCodeProperties.guards w n z b hc)
  have ht : Derives Γ (SyntaxTermSyntax.contexts w b z) := .conjI (.conjR hg) (.conjL hg)
  let T := SyntaxVariableTableSyntax.identity false w.castSucc b.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxVariableTableExistence.identity_exists hZ false w b z hw ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hc1 := of_eq (formulaCode_rename w n z b Fin.castSucc) (under hc T)
  have ht1 := of_eq (SyntaxTermSyntax.contexts_rename w b z Fin.castSucc) (under ht T)
  let V := SyntaxVariableTableSyntax.identity true w.castSucc.castSucc b.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (SyntaxVariableTableExistence.identity_exists (ZFContext.under hZ T) true w.castSucc b.castSucc z.castSucc hw1 ht1)
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hT2 : Derives Ξ (SyntaxVariableTableSyntax.identity false w.castSucc.castSucc b.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [T, Formula.raise, SyntaxVariableTableSyntax.identity_rename]) (under hT V)
  have ho := from_tables (ZFContext.under (ZFContext.under hZ T) V) w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 V)) (of_eq (formulaCode_rename w.castSucc n.castSucc z.castSucc b.castSucc Fin.castSucc) (under hc1 V)) hT2 hV
  exact of_eq (by simp only [Formula.raise, existsReified_rename]) ho

private theorem reify_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n t u : Fin m) (xs ys : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (reifyData w z b n t xs)) (hy : Derives Γ (reifyData w z b n u ys)) : Derives Γ (.equal t u) := by
  have er := SyntaxVariableTableUnique.identity_unique hZ false w b z (xs 0) (ys 0) (.conjL hx) (.conjL hy)
  have es := SyntaxVariableTableUnique.identity_unique hZ true w b z (xs 1) (ys 1) (.conjL (.conjR hx)) (.conjL (.conjR hy))
  have hcR := SyntaxMixedImageCodeUnique.subst_graph w (xs 0) z b z (xs 2) (ys 0) er (.conjL (.conjL (.conjR (.conjR hx))))
  have hcS := SyntaxMixedImageCodeUnique.subst_graph w (xs 1) b b z (xs 3) (ys 1) es (.conjR (.conjL (.conjR (.conjR hx))))
  have eR := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 0) z b z (xs 2) (ys 2) hw hcR (.conjL (.conjL (.conjR (.conjR hy))))
  have eS := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 1) b b z (xs 3) (ys 3) hw hcS (.conjR (.conjL (.conjR (.conjR hy))))
  have hs := SyntaxMixedFormulaJudgmentSubst.subst_s w (ys 2) (xs 3) z b b z n t (ys 3) eS
    (SyntaxMixedFormulaJudgmentSubst.subst_r w (xs 2) (xs 3) z b b z n t (ys 2) eR (.conjR (.conjR (.conjR hx))))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (ys 2) (ys 3) z b b z n t u hw hs (.conjR (.conjR (.conjR hy)))

private theorem reified_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n t u : Fin m) (xs : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (reifyData w z b n t xs)) (hy : Derives Γ (reified w z b n u)) : Derives Γ (.equal t u) := by
  let T := reifyBody w z b n u
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ (.conjR hy)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact reify_data_unique (HornBinderRules.zf_body 4 hZ T) (old 4 w) (old 4 z) (old 4 b) (old 4 n) (old 4 t) (old 4 u) (fun i => old 4 (xs i)) (slot 4)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T))
    (of_eq (reifyData_rename w z b n t xs (old 4)) (HornBinderRules.under_body 4 hx T)) hT

theorem reified_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n t u : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (reified w z b n t)) (hu : Derives Γ (reified w z b n u)) : Derives Γ (.equal t u) := by
  let T := reifyBody w z b n t
  let Δ := Context.add T (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 T _ (.conjR ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact reified_at_data_unique (HornBinderRules.zf_body 4 hZ T) (old 4 w) (old 4 z) (old 4 b) (old 4 n) (old 4 t) (old 4 u) (slot 4)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw T)) hT
    (of_eq (reified_rename w z b n u (old 4)) (HornBinderRules.under_body 4 hu T))

private def data {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (reified w z b n (v 0)).conj ((SyntaxUnaryIterationSyntax.forallClosure w (v 0) b (v 1)).conj
    ((formulaCode w (v 1) z z).conj (ForcingCodeRecursion.compiled R H w z f j z (v 1) Q)))
private theorem data_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (data R H w z f j b n Q v).rename r = data R H (r w) (r z) (r f) (r j) (r b) (r n) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, reified_rename, SyntaxUnaryIterationSyntax.forallClosure_rename, formulaCode_rename, ForcingCodeRecursion.compiled_rename]
private def body {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) : Formula (m+2) :=
  data R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 Q) (slot 2)

/-- Forcing code of the complete universal closure of an open formula. The
source proof free scope b remains arbitrary; every name is bound internally. -/
def compiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) : Formula m :=
  existsMany 2 (body R H w z f j b n Q)
theorem compiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) (r : Fin m → Fin l) :
    (compiled R H w z f j b n Q).rename r = compiled R H (r w) (r z) (r f) (r j) (r b) (r n) (r Q) := by
  simp only [compiled, existsMany_rename, body, data_rename, lift_old, lift_slot]

def existsCompiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) : Formula m := .ex
  (compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m))
theorem existsCompiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R H w z f j b n).rename r = existsCompiled R H (r w) (r z) (r f) (r j) (r b) (r n) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem intro_compiled {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q t c : Fin m)
    (hr : Derives Γ (reified w z b n t)) (hc : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w t b c))
    (ht : Derives Γ (formulaCode w c z z)) (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j z c Q)) :
    Derives Γ (compiled R H w z f j b n Q) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two t c)
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hr (.conjI hc (.conjI ht hq)))

theorem source_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m)
    (hq : Derives Γ (compiled R H w z f j b n Q)) : Derives Γ (formulaCode w n z b) := by
  let T := body R H w z f j b n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w n z b (old 2)).symm (.conjL (.conjL hT))

theorem target_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m)
    (hq : Derives Γ (compiled R H w z f j b n Q)) : Derives Γ (formulaCode w Q z f) := by
  let T := body R H w z f j b n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q z f (old 2)).symm
    (ForcingCodeRecursion.target_type R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 z) (slot 2 1) (old 2 Q) (.conjR (.conjR (.conjR hT))))

private structure Inputs {m} (k : Nat) (Γ : Context m) (w z f j : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
private theorem underInputs {k m} {Γ : Context m} {w z f j : Fin m} (hI : Inputs k Γ w z f j) (T : Formula (m+1)) :
    Inputs k (Context.add T (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc j.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under hI.hw T), of_eq (empty_rename z Fin.castSucc) (under hI.hz T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hI.hf T),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hI.hj T)⟩

private theorem from_closed {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t c : Fin m) (hI : Inputs k Γ w z f j)
    (hr : Derives Γ (reified w z b n t)) (hc : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w t b c))
    (ht : Derives Γ (formulaCode w c z z)) : Derives Γ (existsCompiled R H w z f j b n) := by
  let T := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc z.castSucc c.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingCodeTotal.total hZ R H w z f j z c hI.hw hI.hz hI.hf hI.hj ht)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsCompiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    have hq := intro_compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m) t.castSucc c.castSucc
      (of_eq (reified_rename w z b n t Fin.castSucc) (under hr T))
      (of_eq (SyntaxUnaryIterationSyntax.forallClosure_rename w t b c Fin.castSucc) (under hc T))
      (of_eq (formulaCode_rename w c z z Fin.castSucc) (under ht T)) hT
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsCompiled_rename R H w z f j b n Fin.castSucc).symm ho

private theorem from_reified {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t : Fin m) (hI : Inputs k Γ w z f j) (hr : Derives Γ (reified w z b n t)) : Derives Γ (existsCompiled R H w z f j b n) := by
  let T := (((Formula.mem (Fin.last m) w.castSucc).conj (SyntaxUnaryIterationSyntax.forallClosure w.castSucc t.castSucc b.castSucc (Fin.last m))).conj
    ((formulaCode w.castSucc (Fin.last m) z.castSucc z.castSucc).conj
      (.all ((SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc t.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w n z b (.conjL hr)))
  apply Derives.exE (p := T) (SchemaClosureTyping.closed_fiber hZ w b t z hI.hw hb hI.hz (reified_type w z b n t hr))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := from_closed (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)
    (underInputs hI T) (of_eq (reified_rename w z b n t Fin.castSucc) (under hr T)) (.conjR (.conjL hT)) (.conjL (.conjR hT))
  exact of_eq (existsCompiled_rename R H w z f j b n Fin.castSucc).symm ho

/-- The source free-variable scope is any internal natural, including a
nonstandard one. No environment, renamed code, closure or output is given. -/
theorem total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (formulaCode w n z b)) : Derives Γ (existsCompiled R H w z f j b n) := by
  let T := reified w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (reify_total hZ w z b n hw hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := from_reified (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m) (underInputs ⟨hw,hz,hf,hj⟩ T) hT
  exact of_eq (existsCompiled_rename R H w z f j b n Fin.castSucc).symm ho

private theorem closure_seed_subst {m} {Γ : Context m} (w t b c u : Fin m)
    (he : Derives Γ (.equal t u)) (hc : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w t b c)) :
    Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w u b c) := by
  let P := SyntaxUnaryIterationSyntax.forallClosure w.castSucc (Fin.last m) b.castSucc c.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxUnaryIterationSyntax.forallClosure_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxUnaryIterationSyntax.forallClosure_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))
private theorem code_source_subst {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j c Q d : Fin m)
    (he : Derives Γ (.equal c d)) (hc : Derives Γ (ForcingCodeRecursion.compiled R H w z f j z c Q)) :
    Derives Γ (ForcingCodeRecursion.compiled R H w z f j z d Q) := by
  let P := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc z.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

private theorem data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n Q V : Fin m) (xs ys : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data R H w z f j b n Q xs)) (hy : Derives Γ (data R H w z f j b n V ys)) : Derives Γ (.equal Q V) := by
  have et := reified_unique hZ w z b n (xs 0) (ys 0) hw (.conjL hx) (.conjL hy)
  have hc := closure_seed_subst w (xs 0) b (xs 1) (ys 0) et (.conjL (.conjR hx))
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w n z b (.conjL (.conjL hx))))
  have ec := SyntaxUnaryIterationCore.unique hZ 9 w (ys 0) b (xs 1) (ys 1) hw hb hc (.conjL (.conjR hy))
  have hq := code_source_subst R H w z f j (xs 1) Q (ys 1) ec (.conjR (.conjR (.conjR hx)))
  have hn := Derives.conjL (FormulaCodeProperties.guards w (ys 1) z z (.conjL (.conjR (.conjR hy))))
  exact ForcingCodeUnique.unique hZ R H w z f j z (ys 1) Q V hw hn hq (.conjR (.conjR (.conjR hy)))

private theorem at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n Q V : Fin m) (xs : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data R H w z f j b n Q xs)) (hy : Derives Γ (compiled R H w z f j b n V)) : Derives Γ (.equal Q V) := by
  let T := body R H w z f j b n V
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hy
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 Q) (old 2 V) (fun i => old 2 (xs i)) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (data_rename R H w z f j b n Q xs (old 2)) (HornBinderRules.under_body 2 hx T)) hT

theorem unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled R H w z f j b n Q)) (hv : Derives Γ (compiled R H w z f j b n V)) : Derives Γ (.equal Q V) := by
  let T := body R H w z f j b n Q
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact at_data_unique (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 Q) (old 2 V) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T)) hT
    (of_eq (compiled_rename R H w z f j b n V (old 2)) (HornBinderRules.under_body 2 hv T))

def uniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) : Formula m := .all
  ((compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
theorem uniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R H w z f j b n Q).rename r = uniqueOutput R H (r w) (r z) (r f) (r j) (r b) (r n) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n Q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R H w z f j b n Q)) : Derives Γ (uniqueOutput R H w z f j b n Q) := by
  apply Derives.allI
  apply Derives.impI
  let T := compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (.hyp (Or.inl rfl)) (of_eq (compiled_rename R H w z f j b n Q Fin.castSucc) (under hq T))

def typedUniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) : Formula m := .ex
  ((compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) z.castSucc f.castSucc).conj
      (uniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m))))
theorem typedUniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) (r : Fin m → Fin l) :
    (typedUniqueOutput R H w z f j b n).rename r = typedUniqueOutput R H (r w) (r z) (r f) (r j) (r b) (r n) := by
  simp only [typedUniqueOutput, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typed_unique_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (formulaCode w n z b)) : Derives Γ (typedUniqueOutput R H w z f j b n) := by
  let T := compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (total hZ R H w z f j b n hw hz hf hj hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := target_type R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m) hT
  have hu := unique_output (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hT
  have ho : Derives Δ (typedUniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT (.conjI ht hu))
  exact of_eq (typedUniqueOutput_rename R H w z f j b n Fin.castSucc).symm ho

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp
    ((formulaCode w n z b).imp (typedUniqueOutput R H w z f j b n)))))).close

theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j b n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact typed_unique_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) R H w z f j b n
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def uniqueSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled R H w z f j b n Q).imp ((compiled R H w z f j b n V).imp (.equal Q V)))).close

theorem unique_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence R H w z f j b n Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w z f j b n Q V
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
private theorem reified_in_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b n t r s L S : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxVariableTableSyntax.identity false w b z r))
    (hs : Derives Γ (SyntaxVariableTableSyntax.identity true w b z s))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s z b b z L S))
    (ht : Derives Γ (reified w z b n t)) : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L S z b b z n t) := by
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L.castSucc S.castSucc z.castSucc b.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S z b b z n hw
    (.conjI (.conjL ht) (SyntaxMixedImageCodePairs.term_lists w r s z b b z L S he)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hr1 := of_eq (SyntaxVariableTableSyntax.identity_rename false w b z r Fin.castSucc) (under hr E)
  have hs1 := of_eq (SyntaxVariableTableSyntax.identity_rename true w b z s Fin.castSucc) (under hs E)
  have he1 := of_eq (SyntaxMixedImageCodeSyntax.encodings_rename w r s z b b z L S Fin.castSucc) (under he E)
  have hc1 := of_eq (formulaCode_rename w n z b Fin.castSucc) (under (.conjL ht) E)
  have ht1 := of_eq (reified_rename w z b n t Fin.castSucc) (under ht E)
  let v : Fin 4 → Fin (m+1) := Fin.cases r.castSucc (Fin.cases s.castSucc (SyntaxAtomSyntax.two L.castSucc S.castSucc))
  have hu := intro_reified w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m) v hc1 (.conjI hr1 (.conjI hs1 (.conjI he1 hE)))
  have eq := reified_unique (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m) t.castSucc hw1 hu ht1
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L S z b b z n t Fin.castSucc).symm
    (SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc L.castSucc S.castSucc z.castSucc b.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m) t.castSucc eq hE)

/-- Arbitrary independent reifications preserve all four literal binary nodes.
Use one actual parent environment, then existing totality/uniqueness to align
both child outputs with it. No caller-supplied environment or standard scope. -/
theorem reified_binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w z b n x y Q X Y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hn : Derives Γ (reified w z b n Q)) (hx : Derives Γ (reified w z b x X)) (hy : Derives Γ (reified w z b y Y)) :
    Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y Q) := by
  let E := reifyBody w z b n Q
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (.conjR hn)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ E
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E)
  have he : Derives Δ (SyntaxMixedImageCodeSyntax.encodings (old 4 w) (slot 4 0) (slot 4 1) (old 4 z) (old 4 b) (old 4 b) (old 4 z) (slot 4 2) (slot 4 3)) := .conjL (.conjR (.conjR hE))
  have hx4 := of_eq (reified_rename w z b x X (old 4)) (HornBinderRules.under_body 4 hx E)
  have hy4 := of_eq (reified_rename w z b y Y (old 4)) (HornBinderRules.under_body 4 hy E)
  have hX := reified_in_environment hZ4 (old 4 w) (old 4 z) (old 4 b) (old 4 x) (old 4 X) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    hw4 (.conjL hE) (.conjL (.conjR hE)) he hx4
  have hY := reified_in_environment hZ4 (old 4 w) (old 4 z) (old 4 b) (old 4 y) (old 4 Y) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    hw4 (.conjL hE) (.conjL (.conjR hE)) he hy4
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w X Y Q (old 4)).symm
    (ForcingMixedBinary.binary_constructor hZ4 kind (old 4 w) (slot 4 2) (slot 4 3) (old 4 z) (old 4 b) (old 4 b) (old 4 z)
      (old 4 n) (old 4 x) (old 4 y) (old 4 Q) (old 4 X) (old 4 Y) hw4
      (.conjI (of_eq (formulaCode_rename w n z b (old 4)) (HornBinderRules.under_body 4 (.conjL hn) E))
        (SyntaxMixedImageCodePairs.term_lists _ _ _ _ _ _ _ _ _ he))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n (old 4)) (HornBinderRules.under_body 4 hc E))
      (.conjR (.conjR (.conjR hE))) hX hY)

end PPAC.Migration.ForcingOpenCode
