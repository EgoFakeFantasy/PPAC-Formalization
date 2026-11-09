import PPAC.Migration.ForcingOpenLayout
import PPAC.Migration.ForcingCodeBinary
import PPAC.Migration.ForcingCodeUnary

/-! Pointwise adapter for the pinned source's `forcing_sound` name
assignment. Reify the source free slots, use the ACTUAL forcing compiler with
those bound name slots, then open the names before the fixed parameters.
No universal closure is inserted. Every code and layout witness is internal.
This code-production theorem does not assert preservation of proof rules. -/
namespace PPAC.Migration.ForcingPointwiseCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open NaturalAdditionSyntax (sum sum_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def openData {m} (w z b f t c Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (ForcingOpenLayout.environment w z b f t (v 0) (v 1)).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 0) (v 1) b f z t c Q)
private theorem openData_rename {m l} (w z b f t c Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (openData w z b f t c Q v).rename r = openData (r w) (r z) (r b) (r f) (r t) (r c) (r Q) (fun i => r (v i)) := by
  simp only [openData, Formula.rename, ForcingOpenLayout.environment_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]
private def openBody {m} (w z b f t c Q : Fin m) : Formula (m+2) :=
  openData (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 c) (old 2 Q) (slot 2)
def opened {m} (w z b f t c Q : Fin m) : Formula m := existsMany 2 (openBody w z b f t c Q)
theorem opened_rename {m l} (w z b f t c Q : Fin m) (r : Fin m → Fin l) :
    (opened w z b f t c Q).rename r = opened (r w) (r z) (r b) (r f) (r t) (r c) (r Q) := by
  simp only [opened, existsMany_rename, openBody, openData_rename, lift_old, lift_slot]
private theorem intro_opened {m} {Γ : Context m} (w z b f t c Q L S : Fin m)
    (he : Derives Γ (ForcingOpenLayout.environment w z b f t L S))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L S b f z t c Q)) : Derives Γ (opened w z b f t c Q) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two L S)
  exact of_eq (by simp only [openBody, openData_rename, assign_old, assign_slot]; rfl) (.conjI he hq)

def existsOpened {m} (w z b f t c : Fin m) : Formula m := .ex
  (opened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc c.castSucc (Fin.last m))
theorem existsOpened_rename {m l} (w z b f t c : Fin m) (r : Fin m → Fin l) :
    (existsOpened w z b f t c).rename r = existsOpened (r w) (r z) (r b) (r f) (r t) (r c) := by
  simp only [existsOpened, Formula.rename, opened_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem opened_type {m} {Γ : Context m} (w z b f t c Q : Fin m)
    (ho : Derives Γ (opened w z b f t c Q)) : Derives Γ (formulaCode w Q z t) := by
  let E := openBody w z b f t c Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ ho
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q z t (old 2)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 2 w) (slot 2 0) (slot 2 1) (old 2 b) (old 2 f) (old 2 z) (old 2 t) (old 2 c) (old 2 Q) (.conjR hE))

theorem opened_sum {m} {Γ : Context m} (w z b f t c Q : Fin m)
    (ho : Derives Γ (opened w z b f t c Q)) : Derives Γ (sum w b f t) := by
  let E := openBody w z b f t c Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ ho
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (sum_rename w b f t (old 2)).symm
    (ForcingOpenLayout.environment_sum (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1) (.conjL hE))

private theorem from_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t c L S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w c b f))
    (he : Derives Γ (ForcingOpenLayout.environment w z b f t L S)) : Derives Γ (existsOpened w z b f t c) := by
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L.castSucc S.castSucc b.castSucc f.castSucc z.castSucc t.castSucc c.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S b f z t c hw
    (.conjI hc (ForcingOpenLayout.environment_types w z b f t L S he)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have he1 := of_eq (ForcingOpenLayout.environment_rename w z b f t L S Fin.castSucc) (under he E)
  have hq := intro_opened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc c.castSucc (Fin.last m) L.castSucc S.castSucc he1 hE
  have out : Derives Δ (existsOpened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc c.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, opened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsOpened_rename w z b f t c Fin.castSucc).symm out

theorem opened_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t c : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (hs : Derives Γ (sum w b f t))
    (hc : Derives Γ (formulaCode w c b f)) : Derives Γ (existsOpened w z b f t c) := by
  have hg := Derives.conjR (FormulaCodeProperties.guards w c b f hc)
  let E := ForcingOpenLayout.environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (ForcingOpenLayout.environment_total hZ w z b f t hw hz (.conjL hg) (.conjR hg) hs)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (existsOpened_rename w z b f t c (old 2)).symm
    (from_environment (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 c) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (formulaCode_rename w c b f (old 2)) (HornBinderRules.under_body 2 hc E)) hE)

private def data {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) (v : Fin 2 → Fin m) : Formula m :=
  (ForcingOpenCode.reified w z b n (v 0)).conj
    ((ForcingCodeRecursion.compiled R H w z f j b (v 0) (v 1)).conj (opened w z b f t (v 1) Q))
private theorem data_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) (v : Fin 2 → Fin m) (r : Fin m → Fin l) :
    (data R H w z f j b n t Q v).rename r = data R H (r w) (r z) (r f) (r j) (r b) (r n) (r t) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, ForcingOpenCode.reified_rename, ForcingCodeRecursion.compiled_rename, opened_rename]
private def body {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) : Formula (m+2) :=
  data R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 t) (old 2 Q) (slot 2)

/-- Target slots are names i<b first, then parameter b+i for i<f. -/
def compiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) : Formula m :=
  existsMany 2 (body R H w z f j b n t Q)
theorem compiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) (r : Fin m → Fin l) :
    (compiled R H w z f j b n t Q).rename r = compiled R H (r w) (r z) (r f) (r j) (r b) (r n) (r t) (r Q) := by
  simp only [compiled, existsMany_rename, body, data_rename, lift_old, lift_slot]
def existsCompiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) : Formula m := .ex
  (compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m))
theorem existsCompiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) (r : Fin m → Fin l) :
    (existsCompiled R H w z f j b n t).rename r = existsCompiled R H (r w) (r z) (r f) (r j) (r b) (r n) (r t) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem intro_compiled {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q x c : Fin m)
    (hr : Derives Γ (ForcingOpenCode.reified w z b n x))
    (hc : Derives Γ (ForcingCodeRecursion.compiled R H w z f j b x c))
    (ho : Derives Γ (opened w z b f t c Q)) : Derives Γ (compiled R H w z f j b n t Q) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two x c)
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hr (.conjI hc ho))

theorem source_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m)
    (hq : Derives Γ (compiled R H w z f j b n t Q)) : Derives Γ (formulaCode w n z b) := by
  let E := body R H w z f j b n t Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w n z b (old 2)).symm (.conjL (.conjL hE))
theorem target_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m)
    (hq : Derives Γ (compiled R H w z f j b n t Q)) : Derives Γ (formulaCode w Q z t) := by
  let E := body R H w z f j b n t Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w Q z t (old 2)).symm
    (opened_type (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 1) (old 2 Q) (.conjR (.conjR hE)))

private structure Inputs {m} (k : Nat) (Γ : Context m) (w z f j : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
private theorem underInputs {k m} {Γ : Context m} {w z f j : Fin m} (hI : Inputs k Γ w z f j) (E : Formula (m+1)) :
    Inputs k (Context.add E (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc j.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under hI.hw E), of_eq (empty_rename z Fin.castSucc) (under hI.hz E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hI.hf E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hI.hj E)⟩

private theorem from_raw {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t x c : Fin m) (hI : Inputs k Γ w z f j) (hs : Derives Γ (sum w b f t))
    (hr : Derives Γ (ForcingOpenCode.reified w z b n x))
    (hc : Derives Γ (ForcingCodeRecursion.compiled R H w z f j b x c)) : Derives Γ (existsCompiled R H w z f j b n t) := by
  let E := opened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc c.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hI.hw hI.hz
  apply Derives.exE (p := E) (opened_total hZ w z b f t c hI.hw hzN hs (ForcingCodeRecursion.target_type R H w z f j b x c hc))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr1 := of_eq (ForcingOpenCode.reified_rename w z b n x Fin.castSucc) (under hr E)
  have hc1 := of_eq (ForcingCodeRecursion.compiled_rename R H w z f j b x c Fin.castSucc) (under hc E)
  have hq := intro_compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m) x.castSucc c.castSucc hr1 hc1 hE
  have out : Derives Δ (existsCompiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq (existsCompiled_rename R H w z f j b n t Fin.castSucc).symm out

private theorem from_reified {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t x : Fin m) (hI : Inputs k Γ w z f j) (hs : Derives Γ (sum w b f t))
    (hr : Derives Γ (ForcingOpenCode.reified w z b n x)) : Derives Γ (existsCompiled R H w z f j b n t) := by
  let E := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingCodeTotal.total hZ R H w z f j b x hI.hw hI.hz hI.hf hI.hj (ForcingOpenCode.reified_type w z b n x hr))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := from_raw (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc x.castSucc (Fin.last m)
    (underInputs hI E) (of_eq (sum_rename w b f t Fin.castSucc) (under hs E))
    (of_eq (ForcingOpenCode.reified_rename w z b n x Fin.castSucc) (under hr E)) hE
  exact of_eq (existsCompiled_rename R H w z f j b n t Fin.castSucc).symm out

/-- No external source numeral or external bound length, environment, forcing history or output is
supplied by the caller. The same statement covers nonstandard internal codes. -/
theorem total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hs : Derives Γ (sum w b f t)) (hc : Derives Γ (formulaCode w n z b)) : Derives Γ (existsCompiled R H w z f j b n t) := by
  let E := ForcingOpenCode.reified w.castSucc z.castSucc b.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ForcingOpenCode.reify_total hZ w z b n hw hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := from_reified (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)
    (underInputs ⟨hw,hz,hf,hj⟩ E) (of_eq (sum_rename w b f t Fin.castSucc) (under hs E)) hE
  exact of_eq (existsCompiled_rename R H w z f j b n t Fin.castSucc).symm out

private theorem openData_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t c Q V : Fin m) (v u : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (openData w z b f t c Q v)) (hv : Derives Γ (openData w z b f t c V u)) : Derives Γ (.equal Q V) := by
  have he := ForcingOpenLayout.environment_unique hZ w z b f t (v 0) (v 1) (u 0) (u 1) hw (.conjL hq) (.conjL hv)
  have hV := SyntaxMixedFormulaJudgmentSubst.subst_s w (v 0) (u 1) b f z t c V (v 1) (eq_symm (.conjR he))
    (SyntaxMixedFormulaJudgmentSubst.subst_r w (u 0) (u 1) b f z t c V (v 0) (eq_symm (.conjL he)) (.conjR hv))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (v 0) (v 1) b f z t c Q V hw (.conjR hq) hV
private theorem opened_at_data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t c Q V : Fin m) (v : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (openData w z b f t c Q v)) (hv : Derives Γ (opened w z b f t c V)) : Derives Γ (.equal Q V) := by
  let E := openBody w z b f t c V
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hv
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact openData_unique (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 c) (old 2 Q) (old 2 V)
    (fun i => old 2 (v i)) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (openData_rename w z b f t c Q v (old 2)) (HornBinderRules.under_body 2 hq E)) hE

theorem opened_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t c Q V : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (opened w z b f t c Q)) (hv : Derives Γ (opened w z b f t c V)) : Derives Γ (.equal Q V) := by
  let E := openBody w z b f t c Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact opened_at_data_unique (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 c) (old 2 Q) (old 2 V) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)) hE
    (of_eq (opened_rename w z b f t c V (old 2)) (HornBinderRules.under_body 2 hv E))

private theorem code_source_subst {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b x c y : Fin m)
    (he : Derives Γ (.equal x y)) (hc : Derives Γ (ForcingCodeRecursion.compiled R H w z f j b x c)) :
    Derives Γ (ForcingCodeRecursion.compiled R H w z f j b y c) := by
  let P := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc (Fin.last m) c.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))
private theorem opened_source_subst {m} {Γ : Context m} (w z b f t c Q d : Fin m)
    (he : Derives Γ (.equal c d)) (hq : Derives Γ (opened w z b f t c Q)) : Derives Γ (opened w z b f t d Q) := by
  let P := opened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc (Fin.last m) Q.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, opened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, opened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq))

private theorem data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t Q V : Fin m) (v u : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (data R H w z f j b n t Q v)) (hv : Derives Γ (data R H w z f j b n t V u)) : Derives Γ (.equal Q V) := by
  have hx := ForcingOpenCode.reified_unique hZ w z b n (v 0) (u 0) hw (.conjL hq) (.conjL hv)
  have hC := code_source_subst R H w z f j b (u 0) (u 1) (v 0) (eq_symm hx) (.conjL (.conjR hv))
  have hn := Derives.conjL (FormulaCodeProperties.guards w (v 0) b z (ForcingOpenCode.reified_type w z b n (v 0) (.conjL hq)))
  have hc := ForcingCodeUnique.unique hZ R H w z f j b (v 0) (v 1) (u 1) hw hn (.conjL (.conjR hq)) hC
  exact opened_unique hZ w z b f t (v 1) Q V hw (.conjR (.conjR hq))
    (opened_source_subst w z b f t (u 1) V (v 1) (eq_symm hc) (.conjR (.conjR hv)))
private theorem at_data_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t Q V : Fin m) (v : Fin 2 → Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (data R H w z f j b n t Q v)) (hv : Derives Γ (compiled R H w z f j b n t V)) : Derives Γ (.equal Q V) := by
  let E := body R H w z f j b n t V
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hv
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact data_unique (HornBinderRules.zf_body 2 hZ E) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 t) (old 2 Q) (old 2 V)
    (fun i => old 2 (v i)) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (data_rename R H w z f j b n t Q v (old 2)) (HornBinderRules.under_body 2 hq E)) hE

theorem unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t Q V : Fin m) (hw : Derives Γ (omega w))
    (hq : Derives Γ (compiled R H w z f j b n t Q)) (hv : Derives Γ (compiled R H w z f j b n t V)) : Derives Γ (.equal Q V) := by
  let E := body R H w z f j b n t Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hq
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact at_data_unique (HornBinderRules.zf_body 2 hZ E) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 t) (old 2 Q) (old 2 V) (slot 2)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)) hE
    (of_eq (compiled_rename R H w z f j b n t V (old 2)) (HornBinderRules.under_body 2 hv E))

def uniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) : Formula m := .all
  ((compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
theorem uniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R H w z f j b n t Q).rename r = uniqueOutput R H (r w) (r z) (r f) (r j) (r b) (r n) (r t) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t Q : Fin m) (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled R H w z f j b n t Q)) : Derives Γ (uniqueOutput R H w z f j b n t Q) := by
  apply Derives.allI
  apply Derives.impI
  let E := compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (.hyp (Or.inl rfl)) (of_eq (compiled_rename R H w z f j b n t Q Fin.castSucc) (under hq E))

def typedUniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) : Formula m := .ex
  ((compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) z.castSucc t.castSucc).conj
      (uniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m))))
theorem typedUniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) (r : Fin m → Fin l) :
    (typedUniqueOutput R H w z f j b n t).rename r = typedUniqueOutput R H (r w) (r z) (r f) (r j) (r b) (r n) (r t) := by
  simp only [typedUniqueOutput, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typed_unique_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j b n t : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hs : Derives Γ (sum w b f t)) (hc : Derives Γ (formulaCode w n z b)) : Derives Γ (typedUniqueOutput R H w z f j b n t) := by
  let E := compiled R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (total hZ R H w z f j b n t hw hz hf hj hs hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ht := target_type R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m) hE
  have hu := unique_output (ZFContext.under hZ E) R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) hE
  have out : Derives Δ (typedUniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc b.castSucc n.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [E, Formula.instantiate, Formula.rename, compiled_rename, formulaCode_rename, uniqueOutput_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hE (.conjI ht hu))
  exact of_eq (typedUniqueOutput_rename R H w z f j b n t Fin.castSucc).symm out

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp
    ((sum w b f t).imp ((formulaCode w n z b).imp (typedUniqueOutput R H w z f j b n t))))))).close

theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j b n t)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact typed_unique_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) R H w z f j b n t
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem opened_in_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t n Q L S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f))
    (he : Derives Γ (ForcingOpenLayout.environment w z b f t L S)) (ho : Derives Γ (opened w z b f t n Q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L S b f z t n Q) := by
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L.castSucc S.castSucc b.castSucc f.castSucc z.castSucc t.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S b f z t n hw
    (.conjI hc (ForcingOpenLayout.environment_types w z b f t L S he)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have he1 := of_eq (ForcingOpenLayout.environment_rename w z b f t L S Fin.castSucc) (under he E)
  have ho1 := of_eq (opened_rename w z b f t n Q Fin.castSucc) (under ho E)
  have hu := intro_opened w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc n.castSucc (Fin.last m) L.castSucc S.castSucc he1 hE
  have eq := opened_unique (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc n.castSucc (Fin.last m) Q.castSucc hw1 hu ho1
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L S b f z t n Q Fin.castSucc).symm
    (SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc L.castSucc S.castSucc b.castSucc f.castSucc z.castSucc t.castSucc n.castSucc (Fin.last m) Q.castSucc eq hE)

/-- Actual independent pointwise opening outputs preserve every literal
binary node. All three source types follow from the one parent source type. -/
theorem opened_binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w z b f t n x y Q X Y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (formulaCode w n b f))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hp : Derives Γ (opened w z b f t n Q)) (hx : Derives Γ (opened w z b f t x X)) (hy : Derives Γ (opened w z b f t y Y)) :
    Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y Q) := by
  have ht : Derives Γ (FormulaCodeBranchSyntax.binaryTypes w b f x y) := by
    have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact .impE (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w b f x y n hw hc)) hn
    · exact .impE (.conjL (FormulaCodeKnownLogical.binary1_iff hZ w b f x y n hw hc)) hn
    · exact .impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w b f x y n hw hc)) hn
    · exact .impE (.conjL (FormulaCodeKnownLogical.binary3_iff hZ w b f x y n hw hc)) hn
  let E := openBody w z b f t n Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have he : Derives Δ (ForcingOpenLayout.environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)) := .conjL hE
  have hx2 := of_eq (opened_rename w z b f t x X (old 2)) (HornBinderRules.under_body 2 hx E)
  have hy2 := of_eq (opened_rename w z b f t y Y (old 2)) (HornBinderRules.under_body 2 hy E)
  have hX := opened_in_environment hZ2 (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 x) (old 2 X) (slot 2 0) (slot 2 1)
    hw2 (of_eq (formulaCode_rename w x b f (old 2)) (HornBinderRules.under_body 2 (.conjL (.conjR ht)) E)) he hx2
  have hY := opened_in_environment hZ2 (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (old 2 y) (old 2 Y) (slot 2 0) (slot 2 1)
    hw2 (of_eq (formulaCode_rename w y b f (old 2)) (HornBinderRules.under_body 2 (.conjR (.conjR ht)) E)) he hy2
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w X Y Q (old 2)).symm
    (ForcingMixedBinary.binary_constructor hZ2 kind (old 2 w) (slot 2 0) (slot 2 1) (old 2 b) (old 2 f) (old 2 z) (old 2 t)
      (old 2 n) (old 2 x) (old 2 y) (old 2 Q) (old 2 X) (old 2 Y) hw2
      (.conjI (of_eq (formulaCode_rename w n b f (old 2)) (HornBinderRules.under_body 2 hn E))
        (ForcingOpenLayout.environment_types _ _ _ _ _ _ _ he))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename kind w x y n (old 2)) (HornBinderRules.under_body 2 hc E)) (.conjR hE) hX hY)

private theorem conjunction_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) (v u s : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hp : Derives Γ (data R H w z f j b n t Q v)) (hx : Derives Γ (data R H w z f j b x t X u))
    (hy : Derives Γ (data R H w z f j b y t Y s)) : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w X Y Q) := by
  have hReify := ForcingOpenCode.reified_binary hZ 0 w z b n x y (v 0) (u 0) (s 0) hw hc (.conjL hp) (.conjL hx) (.conjL hy)
  have hn := Derives.conjL (FormulaCodeProperties.guards w (v 0) b z (ForcingOpenCode.reified_type w z b n (v 0) (.conjL hp)))
  have hRaw := ForcingCodeBinary.binary hZ 0 R H w z f j b A B C (v 0) (v 1) (u 0) (s 0) (u 1) (s 1)
    hw hn hA hB hC hReify (.conjL (.conjR hp)) (.conjL (.conjR hx)) (.conjL (.conjR hy))
  exact opened_binary hZ 0 w z b f t (v 1) (u 1) (s 1) Q X Y hw
    (ForcingCodeRecursion.target_type R H w z f j b (v 0) (v 1) (.conjL (.conjR hp))) (.conjL hRaw)
    (.conjR (.conjR hp)) (.conjR (.conjR hx)) (.conjR (.conjR hy))

private theorem conjunction_at_two_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) (v u : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hp : Derives Γ (data R H w z f j b n t Q v)) (hx : Derives Γ (data R H w z f j b x t X u))
    (hy : Derives Γ (compiled R H w z f j b y t Y)) : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w X Y Q) := by
  let E := body R H w z f j b y t Y
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hy
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w X Y Q (old 2)).symm
    (conjunction_data (HornBinderRules.zf_body 2 hZ E) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 x) (old 2 y)
      (old 2 t) (old 2 Q) (old 2 X) (old 2 Y) (old 2 A) (old 2 B) (old 2 C) (fun i => old 2 (v i)) (fun i => old 2 (u i)) (slot 2)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (successor_rename A b (old 2)) (HornBinderRules.under_body 2 hA E))
      (of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hB E))
      (of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hC E))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w x y n (old 2)) (HornBinderRules.under_body 2 hc E))
      (of_eq (data_rename R H w z f j b n t Q v (old 2)) (HornBinderRules.under_body 2 hp E))
      (of_eq (data_rename R H w z f j b x t X u (old 2)) (HornBinderRules.under_body 2 hx E)) hE)

private theorem conjunction_at_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) (v : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hp : Derives Γ (data R H w z f j b n t Q v)) (hx : Derives Γ (compiled R H w z f j b x t X))
    (hy : Derives Γ (compiled R H w z f j b y t Y)) : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w X Y Q) := by
  let E := body R H w z f j b x t X
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hx
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w X Y Q (old 2)).symm
    (conjunction_at_two_data (HornBinderRules.zf_body 2 hZ E) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 x) (old 2 y)
      (old 2 t) (old 2 Q) (old 2 X) (old 2 Y) (old 2 A) (old 2 B) (old 2 C) (fun i => old 2 (v i)) (slot 2)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (successor_rename A b (old 2)) (HornBinderRules.under_body 2 hA E))
      (of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hB E))
      (of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hC E))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w x y n (old 2)) (HornBinderRules.under_body 2 hc E))
      (of_eq (data_rename R H w z f j b n t Q v (old 2)) (HornBinderRules.under_body 2 hp E)) hE
      (of_eq (compiled_rename R H w z f j b y t Y (old 2)) (HornBinderRules.under_body 2 hy E)))

/-- Exact conjunction commutation for arbitrary independently generated
POINTWISE open compilations. Names stay open; b and t may be nonstandard. -/
theorem conjunction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n))
    (hp : Derives Γ (compiled R H w z f j b n t Q)) (hx : Derives Γ (compiled R H w z f j b x t X))
    (hy : Derives Γ (compiled R H w z f j b y t Y)) : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w X Y Q) := by
  let E := body R H w z f j b n t Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w X Y Q (old 2)).symm
    (conjunction_at_data (HornBinderRules.zf_body 2 hZ E) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 x) (old 2 y)
      (old 2 t) (old 2 Q) (old 2 X) (old 2 Y) (old 2 A) (old 2 B) (old 2 C) (slot 2)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (successor_rename A b (old 2)) (HornBinderRules.under_body 2 hA E))
      (of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hB E))
      (of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hC E))
      (of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w x y n (old 2)) (HornBinderRules.under_body 2 hc E)) hE
      (of_eq (compiled_rename R H w z f j b x t X (old 2)) (HornBinderRules.under_body 2 hx E))
      (of_eq (compiled_rename R H w z f j b y t Y (old 2)) (HornBinderRules.under_body 2 hy E)))

def conjunctionInput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) : Formula m :=
  (omega w).conj ((successor A b).conj ((successor B A).conj ((successor C B).conj
    ((SyntaxLogicalSyntax.binaryCode 0 w x y n).conj ((compiled R H w z f j b n t Q).conj
      ((compiled R H w z f j b x t X).conj (compiled R H w z f j b y t Y)))))))
private theorem conjunction_from_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m)
    (hI : Derives Γ (conjunctionInput R H w z f j b n x y t Q X Y A B C)) : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w X Y Q) :=
  conjunction hZ R H w z f j b n x y t Q X Y A B C (.conjL hI) (.conjL (.conjR hI))
    (.conjL (.conjR (.conjR hI))) (.conjL (.conjR (.conjR (.conjR hI))))
    (.conjL (.conjR (.conjR (.conjR (.conjR hI))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hI))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hI)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hI)))))))

/-- Source conjunction introduction/projections are now available on the
ACTUAL pointwise outputs at arbitrary internal open free scope t=b+f. -/
theorem conjunction_iff {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (conjunctionInput R H w z f j b n x y t Q X Y A B C)) :
    Derives Γ ((InternalProofConjunction.proved test w z t Q).iff
      ((InternalProofConjunction.proved test w z t X).conj (InternalProofConjunction.proved test w z t Y))) := by
  have hc := conjunction_from_input hZ R H w z f j b n x y t Q X Y A B C hI
  have hp : Derives Γ (compiled R H w z f j b n t Q) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR hI)))))
  have hb : Derives Γ (ForcingLogicalCode.binary 0 R w z A t j X Y Q) := .conjI hc (target_type R H w z f j b n t Q hp)
  exact InternalProofTemplates.compiled_iff hZ test R w z A t j X Y Q (.conjL hI) hz hb

def conjunctionSentence {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) : Source.Sentence :=
  ((empty z).imp ((conjunctionInput R H w z f j b n x y t Q X Y A B C).imp
    ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t Q).iff
      ((InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t X).conj
        (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t Y))))).close

theorem conjunction_kernel_certificate {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n x y t Q X Y A B C : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (conjunctionSentence target R H w z f j b n x y t Q X Y A B C)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact conjunction_iff (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) (OriginalAxiomCodeTest.test target)
    R H w z f j b n x y t Q X Y A B C (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

/-- The actual name-opening substitution leaves native constants unchanged. -/
theorem opened_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w z b f t n Q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (ho : Derives Γ (opened w z b f t n Q)) : Derives Γ (.equal Q n) := by
  let E := openBody w z b f t n Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ ho
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaNullary.unique (HornBinderRules.zf_body 2 hZ E) truth (old 2 w) (slot 2 0) (slot 2 1)
    (old 2 b) (old 2 f) (old 2 z) (old 2 t) (old 2 n) (old 2 Q)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (SyntaxNodeSyntax.constructor_rename 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n (old 2)) (HornBinderRules.under_body 2 hc E)) (.conjR hE)

private theorem nullary_code_subst {m} {Γ : Context m} (truth : Bool) (w n q : Fin m)
    (he : Derives Γ (.equal n q)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 q) := by
  let P := SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w.castSucc Fin.elim0 (Fin.last m)
  have emptyArgs (v : Fin m) : (fun i : Fin 0 => Fin.lastCases v id (Fin.elim0 i : Fin (m+1))) = (Fin.elim0 : Fin 0 → Fin m) := by
    funext i
    exact Fin.elim0 i
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq, emptyArgs])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq, emptyArgs]) hc))
private theorem nullary_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) (v : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (hp : Derives Γ (data R H w z f j b n t Q v)) : Derives Γ (.equal Q n) := by
  have er := ForcingOpenCode.reified_nullary hZ truth w z b n (v 0) hw hc (.conjL hp)
  have hr := nullary_code_subst truth w n (v 0) (eq_symm er) hc
  have ec := ForcingCodeUnary.nullary hZ truth R H w z f j b A B C (v 0) (v 1) hw
    (ForcingOpenCode.reified_type w z b n (v 0) (.conjL hp)) hA hB hC hr (.conjL (.conjR hp))
  have hraw := nullary_code_subst truth w (v 0) (v 1) (eq_symm ec) hr
  have eo := opened_nullary hZ truth w z b f t (v 1) Q hw hraw (.conjR (.conjR hp))
  exact eq_trans eo (eq_trans ec er)

/-- The actual full pointwise compiler preserves the ORIGINAL constant code,
in particular the exact falsum code needed for the final contradiction path. -/
theorem nullary {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))
    (hp : Derives Γ (compiled R H w z f j b n t Q)) : Derives Γ (.equal Q n) := by
  let E := body R H w z f j b n t Q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact nullary_data (HornBinderRules.zf_body 2 hZ E) truth R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 b) (old 2 n) (old 2 t) (old 2 Q)
    (old 2 A) (old 2 B) (old 2 C) (slot 2) (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (successor_rename A b (old 2)) (HornBinderRules.under_body 2 hA E))
    (of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hB E))
    (of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hC E))
    (of_eq (SyntaxNodeSyntax.constructor_rename 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n (old 2)) (HornBinderRules.under_body 2 hc E)) hE

def nullaryInput {k m} (truth : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) : Formula m :=
  (omega w).conj ((successor A b).conj ((successor B A).conj ((successor C B).conj
    ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).conj (compiled R H w z f j b n t Q)))))
def nullarySentence {k m} (truth : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) : Source.Sentence :=
  ((nullaryInput truth R H w z f j b n t Q A B C).imp (.equal Q n)).close
theorem nullary_kernel_certificate {k m} (truth : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (nullarySentence truth R H w z f j b n t Q A B C)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := nullaryInput truth R H w z f j b n t Q A B C
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact nullary (ZFContext.add (ZFContext.source_ZF m) E) truth R H w z f j b n t Q A B C (.conjL h) (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h))))) (.conjR (.conjR (.conjR (.conjR (.conjR h)))))

/-- Consume the EXACT quoted native falsum occurring in
InternalConsistency.contradiction, rather than a replacement target formula. -/
theorem falsum {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hn : Derives Γ (PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w n))
    (hp : Derives Γ (compiled R H w z f j b n t Q)) : Derives Γ (.equal Q n) :=
  nullary hZ false R H w z f j b n t Q A B C hw hA hB hC
    (OriginalQuotationNodeFields.tree_to_constructor hZ 0 List.nil w n Fin.elim0 hw (.eqRefl w) hn) hp

def falsumSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A b).imp ((successor B A).imp ((successor C B).imp
    ((PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w n).imp
      ((compiled R H w z f j b n t Q).imp (.equal Q n))))))).close

theorem falsum_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b n t Q A B C : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (falsumSentence R H w z f j b n t Q A B C)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact falsum (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _)
    R H w z f j b n t Q A B C (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingPointwiseCode
