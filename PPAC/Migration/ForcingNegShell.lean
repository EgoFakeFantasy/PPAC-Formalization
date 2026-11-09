import PPAC.Migration.ForcingFormulaCancellation
import PPAC.Migration.ForcingNegCode

/-! The three literal IMP nodes of the original negative compiler, under the
actual mixed substitutions. Every child output is an object witness. Guard
validity and normalized forcing modus ponens are not asserted here. -/
namespace PPAC.Migration.ForcingNegShell
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Target slots: member guard, order guard, operand, bottom, inner IMP,
middle IMP. The final parent is the actual supplied operation output. -/
def chainData {m} (w R S a b c d M O C B U : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w (v 0) (v 5) U).conj
    ((SyntaxLogicalSyntax.binaryCode 2 w (v 1) (v 4) (v 5)).conj
      ((SyntaxLogicalSyntax.binaryCode 2 w (v 2) (v 3) (v 4)).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d M (v 0)).conj
          ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d O (v 1)).conj
            ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d C (v 2)).conj
              (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d B (v 3)))))))

theorem chainData_rename {m l} (w R S a b c d M O C B U : Fin m) (v : Fin 6 → Fin m) (r : Fin m → Fin l) :
    (chainData w R S a b c d M O C B U v).rename r =
      chainData (r w) (r R) (r S) (r a) (r b) (r c) (r d) (r M) (r O) (r C) (r B) (r U) (fun i => r (v i)) := by
  simp only [chainData, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def chainBody {m} (w R S a b c d M O C B U : Fin m) : Formula (m+6) :=
  chainData (old 6 w) (old 6 R) (old 6 S) (old 6 a) (old 6 b) (old 6 c) (old 6 d)
    (old 6 M) (old 6 O) (old 6 C) (old 6 B) (old 6 U) (slot 6)
def chain {m} (w R S a b c d M O C B U : Fin m) : Formula m :=
  existsMany 6 (chainBody w R S a b c d M O C B U)

theorem chain_rename {m l} (w R S a b c d M O C B U : Fin m) (r : Fin m → Fin l) :
    (chain w R S a b c d M O C B U).rename r =
      chain (r w) (r R) (r S) (r a) (r b) (r c) (r d) (r M) (r O) (r C) (r B) (r U) := by
  simp only [chain, existsMany_rename, chainBody, chainData_rename, lift_old, lift_slot]

/-- Extract all six actual target fields by consuming the original binary
output lemma three times, without assuming any child-output answer. -/
theorem transform {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d M O C B N I J U : Fin m)
    (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w C B N))
    (hI : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w O N I))
    (hJ : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w M I J))
    (hp : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d J U)) :
    Derives Γ (chain w R S a b c d M O C B U) := by
  have he0 := ForcingFormulaDiagram.binary_output hZ 2 w R S a b c d J M I U hw hJ hp
  let E0 := ForcingFormulaDiagram.binaryBody 2 w R S a b c d M I U
  let Δ1 := Context.add E0 (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E0 _ he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ E0
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E0)
  have hI1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 2 w O N I (old 2)) (HornBinderRules.under_body 2 hI E0)
  have he1 := ForcingFormulaDiagram.binary_output hZ1 2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 I) (old 2 O) (old 2 N) (slot 2 1) hw1 hI1 (.conjR (.conjR hE0))
  let E1 := ForcingFormulaDiagram.binaryBody 2 (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 O) (old 2 N) (slot 2 1)
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hN2 : Derives Δ2 (SyntaxLogicalSyntax.binaryCode 2 (old 2 (old 2 w)) (old 2 (old 2 C)) (old 2 (old 2 B)) (old 2 (old 2 N))) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename])
    (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hN E0) E1)
  have he2 := ForcingFormulaDiagram.binary_output hZ2 2 (old 2 (old 2 w)) (old 2 (old 2 R)) (old 2 (old 2 S))
    (old 2 (old 2 a)) (old 2 (old 2 b)) (old 2 (old 2 c)) (old 2 (old 2 d))
    (old 2 (old 2 N)) (old 2 (old 2 C)) (old 2 (old 2 B)) (slot 2 1) hw2 hN2 (.conjR (.conjR hE1))
  let E2 := ForcingFormulaDiagram.binaryBody 2 (old 2 (old 2 w)) (old 2 (old 2 R)) (old 2 (old 2 S))
    (old 2 (old 2 a)) (old 2 (old 2 b)) (old 2 (old 2 c)) (old 2 (old 2 d))
    (old 2 (old 2 C)) (old 2 (old 2 B)) (slot 2 1)
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hB0 := HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hE0 E1) E2
  have hB1 := HornBinderRules.under_body 2 hE1 E2
  let v : Fin 6 → Fin (m+6) := Fin.cases (old 2 (old 2 (slot 2 0)))
    (Fin.cases (old 2 (slot 2 0)) (Fin.cases (slot 2 0)
      (Fin.cases (slot 2 1) (Fin.cases (old 2 (slot 2 1)) (fun _ => old 2 (old 2 (slot 2 1)))))))
  have hout : Derives Δ3 (chain (old 6 w) (old 6 R) (old 6 S) (old 6 a) (old 6 b) (old 6 c) (old 6 d)
      (old 6 M) (old 6 O) (old 6 C) (old 6 B) (old 6 U)) := by
    apply HornBinderRules.intro_many 6 _ v
    exact of_eq (by simp only [chainBody, assign_old, assign_slot, chainData, Formula.rename,
      SyntaxLogicalSyntax.binaryCode_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl)
      (.conjI (.conjL hB0) (.conjI (.conjL hB1) (.conjI (.conjL hE2)
        (.conjI (.conjL (.conjR hB0)) (.conjI (.conjL (.conjR hB1))
          (.conjI (.conjL (.conjR hE2)) (.conjR (.conjR hE2))))))))
  exact of_eq (by simp only [chain_rename]; rfl) hout

/-- Only actual root operations and the selected original condition field.
No guard truth, derived operand equality, or child induction premise. -/
def cancellationBase {m} (w mode z a f T A C R S K H j n q P r s D : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((ForcingConditionRebind.compiled w a f A j n q).conj ((Formula.mem j f).conj ((StructuralListFieldSyntax.field w S j P).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n D))))))))))

theorem cancellationBase_rename {m l} (w mode z a f T A C R S K H j n q P r s D : Fin m) (ρ : Fin m → Fin l) :
    (cancellationBase w mode z a f T A C R S K H j n q P r s D).rename ρ = cancellationBase (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ q) (ρ P) (ρ r) (ρ s) (ρ D) := by
  simp only [cancellationBase, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename,
    empty_rename, ForcingOpenLayout.environment_rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    ForcingConditionRebind.compiled_rename, StructuralListFieldSyntax.field_rename,
    SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem cancel_operand {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q P r s D I Y : Fin m)
    (hb : Derives Γ (cancellationBase w mode z a f T A C R S K H j n q P r s D))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q I))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T I Y)) : Derives Γ (.equal Y D) := by
  have hw := Derives.conjL hb
  have hm := Derives.conjL (.conjR hb)
  have hz := Derives.conjL (.conjR (.conjR hb))
  have he := Derives.conjL (.conjR (.conjR (.conjR hb)))
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hb))))
  have hc := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))
  have hj := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb))))))
  have hp := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb))))))))
  have hd := (Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hb)))))))))
  have htop := Derives.impE (.conjR (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P I Y r s hw ht)) hi
  have htype := SyntaxMixedFormulaJudgment.target_type w K H A f C T q I ho
  have hrun := Derives.impE (.conjR (InstantiateTopFormulaOperation.at_codes_iff hZ w mode z P T C r s I Y hw hm hz ht htype)) htop
  exact ForcingFormulaCancellation.from_compiled hZ w mode z a f T A C R S K H j n q I Y D P r s
    hw hm hz he hl hc hj hp ht ho hrun hd

def finalData {m} (w r s C T z Y D B : Fin m) (v u : Fin 6 → Fin m) : Formula m :=
  (chainData w r s C T z T (v 0) (v 1) (v 2) (v 3) Y u).conj
    ((Formula.equal (u 2) D).conj (.equal (u 3) B))
theorem finalData_rename {m l} (w r s C T z Y D B : Fin m) (v u : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (finalData w r s C T z Y D B v u).rename ρ =
      finalData (ρ w) (ρ r) (ρ s) (ρ C) (ρ T) (ρ z) (ρ Y) (ρ D) (ρ B) (fun i => ρ (v i)) (fun i => ρ (u i)) := by
  simp only [finalData, Formula.rename, chainData_rename]
def finalBody {m} (w r s C T z Y D B : Fin m) (v : Fin 6 → Fin m) : Formula (m+6) :=
  finalData (old 6 w) (old 6 r) (old 6 s) (old 6 C) (old 6 T) (old 6 z) (old 6 Y) (old 6 D) (old 6 B)
    (fun i => old 6 (v i)) (slot 6)
def finalFields {m} (w r s C T z Y D B : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  existsMany 6 (finalBody w r s C T z Y D B v)
theorem finalFields_rename {m l} (w r s C T z Y D B : Fin m) (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (finalFields w r s C T z Y D B v).rename ρ =
      finalFields (ρ w) (ρ r) (ρ s) (ρ C) (ρ T) (ρ z) (ρ Y) (ρ D) (ρ B) (fun i => ρ (v i)) := by
  simp only [finalFields, existsMany_rename, finalBody, finalData_rename, lift_old, lift_slot]

private theorem second {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q P r s D M O B F Y : Fin m) (v : Fin 6 → Fin m)
    (hb : Derives Γ (cancellationBase w mode z a f T A C R S K H j n q P r s D))
    (hB : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 B))
    (hv : Derives Γ (chainData w K H A f C T M O q B F v))
    (hp : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (finalFields w r s C T z Y D B v) := by
  have hw := Derives.conjL hb
  have he := transform hZ w r s C T z T (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) F Y hw
    (.conjL (.conjR (.conjR hv))) (.conjL (.conjR hv)) (.conjL hv) hp
  let E := chainBody w r s C T z T (v 0) (v 1) (v 2) (v 3) Y
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ6 := HornBinderRules.zf_body 6 hZ E
  have hb6 := of_eq (cancellationBase_rename w mode z a f T A C R S K H j n q P r s D (old 6)) (HornBinderRules.under_body 6 hb E)
  have hv6 := of_eq (chainData_rename w K H A f C T M O q B F v (old 6)) (HornBinderRules.under_body 6 hv E)
  have hB6 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (old 6 w) Fin.elim0 (old 6 B)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (HornBinderRules.under_body 6 hB E)
  have eqOperand := cancel_operand hZ6 (old 6 w) (old 6 mode) (old 6 z) (old 6 a) (old 6 f) (old 6 T) (old 6 A) (old 6 C) (old 6 R) (old 6 S) (old 6 K) (old 6 H) (old 6 j) (old 6 n) (old 6 q) (old 6 P) (old 6 r) (old 6 s) (old 6 D) (old 6 (v 2)) (slot 6 2) hb6
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hv6))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hE))))))
  have eqB := SyntaxMixedFormulaNullary.unique hZ6 false (old 6 w) (old 6 K) (old 6 H)
    (old 6 A) (old 6 f) (old 6 C) (old 6 T) (old 6 B) (old 6 (v 3)) (.conjL hb6) hB6
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hv6))))))
  have hLast := SyntaxMixedFormulaJudgmentSubst.subst_n (old 6 w) (old 6 r) (old 6 s) (old 6 C) (old 6 T)
    (old 6 z) (old 6 T) (old 6 (v 3)) (slot 6 3) (old 6 B) eqB
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hE))))))
  have eqBottom := SyntaxMixedFormulaNullary.unique hZ6 false (old 6 w) (old 6 r) (old 6 s)
    (old 6 C) (old 6 T) (old 6 z) (old 6 T) (old 6 B) (slot 6 3) (.conjL hb6) hB6 hLast
  have hout : Derives Δ (finalFields (old 6 w) (old 6 r) (old 6 s) (old 6 C) (old 6 T)
      (old 6 z) (old 6 Y) (old 6 D) (old 6 B) (fun i => old 6 (v i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [finalBody, finalData_rename, assign_old, assign_slot]; rfl)
      (.conjI hE (.conjI eqOperand eqBottom))
  exact of_eq (finalFields_rename w r s C T z Y D B v (old 6)).symm hout

def normalizedData {m} (w K H A f C T M O q B F r s z Y D : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (chainData w K H A f C T M O q B F v).conj (finalFields w r s C T z Y D B v)
theorem normalizedData_rename {m l} (w K H A f C T M O q B F r s z Y D : Fin m) (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (normalizedData w K H A f C T M O q B F r s z Y D v).rename ρ =
      normalizedData (ρ w) (ρ K) (ρ H) (ρ A) (ρ f) (ρ C) (ρ T) (ρ M) (ρ O) (ρ q) (ρ B) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) (fun i => ρ (v i)) := by
  simp only [normalizedData, Formula.rename, chainData_rename, finalFields_rename]
def normalizedBody {m} (w K H A f C T M O q B F r s z Y D : Fin m) : Formula (m+6) :=
  normalizedData (old 6 w) (old 6 K) (old 6 H) (old 6 A) (old 6 f) (old 6 C) (old 6 T) (old 6 M) (old 6 O) (old 6 q) (old 6 B) (old 6 F) (old 6 r) (old 6 s) (old 6 z) (old 6 Y) (old 6 D) (slot 6)
def normalized {m} (w K H A f C T M O q B F r s z Y D : Fin m) : Formula m :=
  existsMany 6 (normalizedBody w K H A f C T M O q B F r s z Y D)
theorem normalized_rename {m l} (w K H A f C T M O q B F r s z Y D : Fin m) (ρ : Fin m → Fin l) :
    (normalized w K H A f C T M O q B F r s z Y D).rename ρ =
      normalized (ρ w) (ρ K) (ρ H) (ρ A) (ρ f) (ρ C) (ρ T) (ρ M) (ρ O) (ρ q) (ρ B) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) := by
  simp only [normalized, existsMany_rename, normalizedBody, normalizedData_rename, lift_old, lift_slot]

/-- Both stages' fields are internal. The final operand equals the actual
direct opening, and bottom is the SAME original falsum code. The two guards
retain their actual substitution judgments; their truth is not assumed. -/
theorem normalize {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q P r s D M O B N I J F Y : Fin m)
    (hb : Derives Γ (cancellationBase w mode z a f T A C R S K H j n q P r s D))
    (hB : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 B))
    (hN : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w q B N))
    (hI : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w O N I))
    (hJ : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w M I J))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (normalized w K H A f C T M O q B F r s z Y D) := by
  have he := transform hZ w K H A f C T M O q B N I J F (.conjL hb) hN hI hJ ho
  let E := chainBody w K H A f C T M O q B F
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hb6 := of_eq (cancellationBase_rename w mode z a f T A C R S K H j n q P r s D (old 6)) (HornBinderRules.under_body 6 hb E)
  have hB6 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (old 6 w) Fin.elim0 (old 6 B)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]) (HornBinderRules.under_body 6 hB E)
  have hi6 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T F Y (old 6)) (HornBinderRules.under_body 6 hi E)
  have hf := second (HornBinderRules.zf_body 6 hZ E) (old 6 w) (old 6 mode) (old 6 z) (old 6 a) (old 6 f) (old 6 T) (old 6 A) (old 6 C) (old 6 R) (old 6 S) (old 6 K) (old 6 H) (old 6 j) (old 6 n) (old 6 q) (old 6 P) (old 6 r) (old 6 s) (old 6 D) (old 6 M) (old 6 O) (old 6 B) (old 6 F) (old 6 Y) (slot 6) hb6 hB6 hE hi6
  have hout : Derives Δ (normalized (old 6 w) (old 6 K) (old 6 H) (old 6 A) (old 6 f) (old 6 C) (old 6 T) (old 6 M) (old 6 O) (old 6 q) (old 6 B) (old 6 F) (old 6 r) (old 6 s) (old 6 z) (old 6 Y) (old 6 D)) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [normalizedBody, normalizedData_rename, assign_old, assign_slot]; rfl) (.conjI hE hf)
  exact of_eq (normalized_rename w K H A f C T M O q B F r s z Y D (old 6)).symm hout

end PPAC.Migration.ForcingNegShell
