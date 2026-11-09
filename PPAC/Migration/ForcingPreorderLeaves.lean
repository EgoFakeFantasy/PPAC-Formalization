import PPAC.Migration.ForcingRelationRawFormula

/-! Extract SAME five-tail / six-leaf mixed queries from the original raw
preorder and SAME actual matrix/background record. Native instances and
internal proof witnesses are retained. No replacement row, leaf/query/code
answer, guard truth, new kernel/checker/recursion/induction is supplied. -/
namespace PPAC.Migration.ForcingPreorderLeaves
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def quad {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private theorem quad_map {m l} (a b c d : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (quad a b c d i)) = quad (ρ a) (ρ b) (ρ c) (ρ d) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i

def leafSlot (i : Fin 6) : Fin 16 := ⟨10+i.val, by omega⟩
def tailSlot (i : Fin 5) : Fin 16 := ⟨5+i.val, by omega⟩

def queries {m} (w D S A3 f z T : Fin m) (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (substituted w D S A3 f z T (v 5) (N 0)).conj ((substituted w D S A3 f z T (v 6) (N 1)).conj ((substituted w D S A3 f z T (v 7) (N 2)).conj ((substituted w D S A3 f z T (v 8) (N 3)).conj ((substituted w D S A3 f z T (v 9) (N 4)).conj ((substituted w D S A3 f z T (v 10) (H 0)).conj ((substituted w D S A3 f z T (v 11) (H 1)).conj ((substituted w D S A3 f z T (v 12) (H 2)).conj ((substituted w D S A3 f z T (v 13) (H 3)).conj ((substituted w D S A3 f z T (v 14) (H 4)).conj ((substituted w D S A3 f z T (v 15) (H 5))))))))))))

theorem queries_rename {m l} (w D S A3 f z T : Fin m) (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (queries w D S A3 f z T v H N).rename ρ = queries (ρ w) (ρ D) (ρ S) (ρ A3) (ρ f) (ρ z) (ρ T)
      (fun i => ρ (v i)) (fun i => ρ (H i)) (fun i => ρ (N i)) := by
  simp only [queries, Formula.rename, substituted_rename]

/-- All ELEVEN queries follow the ACTUAL source/target IMP fields to the
SAME leaves/tails, not independently generated or selected outputs. -/
theorem extract {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C Refl Pre D S : Fin m) (v : Fin 16 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (hRow : Derives Γ (ForcingTransitiveGuardProof.row w z T C Refl Pre G H U F P N))
    (h0 : Derives Γ (substituted w D S A3 f z T (v 5) (N 0))) :
    Derives Γ (queries w D S A3 f z T v H N) := by
  have hs0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))))
  have ht0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))))))
  have hi0 := SyntaxMixedFormulaOutput.input_of_substituted hZ w D S A3 f z T (v 5) (N 0) hw h0
  have hPair0 := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w D S A3 f z T (v 5) (N 0) (v 10) (v 6) (H 0) (N 1) hw hi0 hs0 ht0)) h0
  have hl0 := Derives.conjL hPair0
  have h1 := Derives.conjR hPair0
  have hs1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))
  have ht1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))))))))
  have hi1 := SyntaxMixedFormulaOutput.input_of_substituted hZ w D S A3 f z T (v 6) (N 1) hw h1
  have hPair1 := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w D S A3 f z T (v 6) (N 1) (v 11) (v 7) (H 1) (N 2) hw hi1 hs1 ht1)) h1
  have hl1 := Derives.conjL hPair1
  have h2 := Derives.conjR hPair1
  have hs2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))))))
  have ht2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))))))))
  have hi2 := SyntaxMixedFormulaOutput.input_of_substituted hZ w D S A3 f z T (v 7) (N 2) hw h2
  have hPair2 := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w D S A3 f z T (v 7) (N 2) (v 12) (v 8) (H 2) (N 3) hw hi2 hs2 ht2)) h2
  have hl2 := Derives.conjL hPair2
  have h3 := Derives.conjR hPair2
  have hs3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))))
  have ht3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))))))))))
  have hi3 := SyntaxMixedFormulaOutput.input_of_substituted hZ w D S A3 f z T (v 8) (N 3) hw h3
  have hPair3 := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w D S A3 f z T (v 8) (N 3) (v 13) (v 9) (H 3) (N 4) hw hi3 hs3 ht3)) h3
  have hl3 := Derives.conjL hPair3
  have h4 := Derives.conjR hPair3
  have hs4 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))))
  have ht4 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))))))))))
  have hi4 := SyntaxMixedFormulaOutput.input_of_substituted hZ w D S A3 f z T (v 9) (N 4) hw h4
  have hPair4 := Derives.impE (Derives.conjL (SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w D S A3 f z T (v 9) (N 4) (v 14) (v 15) (H 4) (H 5) hw hi4 hs4 ht4)) h4
  have hl4 := Derives.conjL hPair4
  have h5 := Derives.conjR hPair4
  exact (.conjI h0 (.conjI h1 (.conjI h2 (.conjI h3 (.conjI h4 (.conjI hl0 (.conjI hl1 (.conjI hl2 (.conjI hl3 (.conjI hl4 h5))))))))))

theorem leaf_at {m} {Γ : Context m} (w D S A3 f z T : Fin m) (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) (i : Fin 6)
    (h : Derives Γ (queries w D S A3 f z T v H N)) : Derives Γ (substituted w D S A3 f z T (v (leafSlot i)) (H i)) := by
  rcases i with ⟨i,hi⟩
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))
  · exact (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))

/-- Whole original raw record and SAME background/proof record are kept
alongside the generated prefix and query record. -/
def data {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (ForcingPreorderCode.rawData R w z A1 A2 A3 f v).conj
    ((ForcingPreorderInstances.backgroundData test w z T C Refl Pre G H U F P N).conj
      ((substituted w B S z f z T (v 2) (U 0)).conj
      ((ForcingPreorderPrefix.data w z f T B S (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) (quad (U 0) (U 1) (U 2) (N 0)) P D).conj
        (queries w (D 2) S A3 f z T v H N))))

theorem data_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (data test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N D).rename ρ =
    data test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre)
      (fun i => ρ (v i)) (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) (fun i => ρ (D i)) := by
  simp only [data, Formula.rename, ForcingPreorderCode.rawData_rename, ForcingPreorderInstances.backgroundData_rename,
    ForcingPreorderPrefix.data_rename, substituted_rename, queries_rename, quad_map]

def body {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula (m+3) :=
  data test R (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f) (old 3 T) (old 3 C) (old 3 B) (old 3 S) (old 3 Refl) (old 3 Pre)
    (fun i => old 3 (v i)) (fun i => old 3 (G i)) (fun i => old 3 (H i)) (fun i => old 3 (U i)) (fun i => old 3 (F i)) (fun i => old 3 (P i)) (fun i => old 3 (N i)) (slot 3)

def produced {k m} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  existsMany 3 (body test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N)

theorem produced_rename {k m l} (test : Formula 1) (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre : Fin m)
    (v : Fin 16 → Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (produced test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N).rename ρ =
    produced test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ Refl) (ρ Pre)
      (fun i => ρ (v i)) (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- Use the SAME original row's native instances to generate all three
prefix tables; recover its own actual matrix query and all eleven children.
The existing proof/background record and source rawData are retained. -/
theorem from_row {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre : Fin m) (v : Fin 16 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA1 : Derives Γ (successor A1 z)) (hA2 : Derives Γ (successor A2 A1)) (hA3 : Derives Γ (successor A3 A2))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (hb : Derives Γ (ForcingPreorderInstances.backgroundData test w z T C Refl Pre G H U F P N))
    (hp : Derives Γ (substituted w B S z f z T (v 2) (U 0))) :
    Derives Γ (produced test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N) := by
  have hRow := Derives.conjL hb
  have hs0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))
  have hs1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))
  have hs2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))
  have ht0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))
  have ht1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))
  have ht2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))
  have ht3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))))
  have ht4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))))
  have ht5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))))))))

  have hLists := Derives.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hp)
  have hBasis : Derives Γ (ForcingPreorderPrefix.basis w z f T B S (U 0) (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5))) :=
    .conjI hw (.conjI hz (.conjI hLists (.conjI hp (.conjI (.conjI hA1 hs0) (.conjI (.conjI hA2 hs1) (.conjI hA3 hs2))))))
  have hInput : Derives Γ (ForcingPreorderPrefix.input w z f T C B S (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5))
      (quad (U 0) (U 1) (U 2) (N 0)) F P) :=
    .conjI hBasis (.conjI (.conjI ht0 ht1) (.conjI (.conjI ht2 ht3) (.conjI ht4 ht5)))
  have hex := ForcingPreorderPrefix.produce hZ w z f T C B S (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5))
    (quad (U 0) (U 1) (U 2) (N 0)) F P hInput
  let E := ForcingPreorderPrefix.body w z f T B S (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) (quad (U 0) (U 1) (U 2) (N 0)) P
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ E
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw E)
  have hr3 := of_eq (ForcingPreorderCode.rawData_rename R w z A1 A2 A3 f v (old 3)) (HornBinderRules.under_body 3 hr E)
  have hb3 := of_eq (ForcingPreorderInstances.backgroundData_rename test w z T C Refl Pre G H U F P N (old 3)) (HornBinderRules.under_body 3 hb E)
  have hp3 := of_eq (substituted_rename w B S z f z T (v 2) (U 0) (old 3)) (HornBinderRules.under_body 3 hp E)
  have hMatrix := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hE)))
  have hQueries := extract hZ3 R (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f) (old 3 T) (old 3 C) (old 3 Refl) (old 3 Pre) (slot 3 2) (old 3 S)
    (fun i => old 3 (v i)) (fun i => old 3 (G i)) (fun i => old 3 (H i)) (fun i => old 3 (U i)) (fun i => old 3 (F i)) (fun i => old 3 (P i)) (fun i => old 3 (N i)) hw3 hr3 (Derives.conjL hb3) hMatrix
  have hData : Derives Δ (data test R (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f) (old 3 T) (old 3 C) (old 3 B) (old 3 S) (old 3 Refl) (old 3 Pre)
      (fun i => old 3 (v i)) (fun i => old 3 (G i)) (fun i => old 3 (H i)) (fun i => old 3 (U i)) (fun i => old 3 (F i)) (fun i => old 3 (P i)) (fun i => old 3 (N i)) (slot 3)) :=
    .conjI hr3 (.conjI hb3 (.conjI hp3 (.conjI hE hQueries)))
  have hout : Derives Δ (produced test R (old 3 w) (old 3 z) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 f) (old 3 T) (old 3 C) (old 3 B) (old 3 S) (old 3 Refl) (old 3 Pre)
      (fun i => old 3 (v i)) (fun i => old 3 (G i)) (fun i => old 3 (H i)) (fun i => old 3 (U i)) (fun i => old 3 (F i)) (fun i => old 3 (P i)) (fun i => old 3 (N i))) := by
    apply HornBinderRules.intro_many 3 _ (slot 3)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot] <;> rfl) hData
  exact of_eq (by simp only [produced_rename] <;> rfl) hout

private theorem numeral_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (x y : Fin m)
    (hx : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) x)) (hy : Derives Γ (SyntaxNumeralSyntax.numeral k y)) :
    Derives Γ (successor x y) := by
  let E := (SyntaxNumeralSyntax.numeral k (Fin.last m)).conj (successor x.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ k x _ hx
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hy1 := of_eq (SyntaxNumeralSyntax.numeral_rename k y Fin.castSucc) (under hy E)
  have hEq := SyntaxNumerals.unique (ZFContext.under hZ E) k (Fin.last m) y.castSucc (Derives.conjL hE) hy1
  exact of_eq (successor_rename x y Fin.castSucc).symm
    (GodelUnpairArithmetic.successor_base_subst x.castSucc (Fin.last m) y.castSucc hEq (Derives.conjR hE))

/-- Original source profile successors are derived from their actual
numerals using existing numeral uniqueness and successor transport. -/
theorem from_numbers {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre : Fin m) (v : Fin 16 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v))
    (hb : Derives Γ (ForcingPreorderInstances.backgroundData test w z T C Refl Pre G H U F P N))
    (hp : Derives Γ (substituted w B S z f z T (v 2) (U 0))) :
    Derives Γ (produced test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N) :=
  from_row hZ test R w z A1 A2 A3 f T C B S Refl Pre v G H U F P N hw hz
    (numeral_step hZ 0 A1 z hA1 hz) (numeral_step hZ 1 A2 A1 hA2 hA1) (numeral_step hZ 2 A3 A2 hA3 hA2) hr hb hp

theorem tail_at {m} {Γ : Context m} (w D S A3 f z T : Fin m) (v : Fin 16 → Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) (i : Fin 5)
    (h : Derives Γ (queries w D S A3 f z T v H N)) : Derives Γ (substituted w D S A3 f z T (v (tailSlot i)) (N i)) := by
  rcases i with ⟨i,hi⟩
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl
  · exact (Derives.conjL h)
  · exact (Derives.conjL (Derives.conjR h))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR h)))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))
  · exact (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))

private theorem term_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) : Derives Γ (.mem n w) := by
  apply Derives.disjE (Derives.conjR ht)
  · exact SyntaxTermBranches.range (ZFContext.add hZ _) true w a n (add hw _) (.hyp (Or.inl rfl))
  · exact SyntaxTermBranches.range (ZFContext.add hZ _) false w b n (add hw _) (.hyp (Or.inl rfl))

def relationPosition (i : Fin 3) : Fin 6 := ⟨3+i.val, by omega⟩
theorem relation_slot (i : Fin 3) : leafSlot (relationPosition i) = ForcingRelationSource.rawSlot i := by
  rcases i with ⟨i,hi⟩
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

/-- Natural condition-term codes follow from SAME row's actual three
native instantiations, using the existing term branch range theorem. -/
theorem conditions_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z T C Refl Pre : Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hRow : Derives Γ (ForcingTransitiveGuardProof.row w z T C Refl Pre Gb H U F P N)) :
    ∀ i : Fin 3, Derives Γ (.mem (P i) w) := by
  have hTerm0 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 0) (F 0) (U 1) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))
  have hP0 := term_natural hZ w z T (P 0) hw hTerm0
  have hTerm1 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 1) (F 1) (U 2) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))))
  have hP1 := term_natural hZ w z T (P 1) hw hTerm1
  have hTerm2 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 2) (F 2) (N 0) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))))))))))
  have hP2 := term_natural hZ w z T (P 2) hw hTerm2

  have hP : ∀ i : Fin 3, Derives Γ (.mem (P i) w) := by
    intro i
    rcases i with ⟨i,hi⟩
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact hP0
    · exact hP1
    · exact hP2
  exact hP

/-- Consume generated SAME-row queries: recover original empty-table type
and condition-term naturality from retained parent/native records, extract
its own raw relation query and use the already proved relation_leaf bridge.
No raw leaf-query, term-range, empty-table or code-equality answer supplied. -/
theorem relation_from_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (k+2)) (leaf : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre g Gc X i j M W Vg K vg : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (D : Fin 3 → Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hd : Derives Γ (data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z g A3 f (v (ForcingRelationSource.rawSlot leaf)) Gc X E))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf))
      (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) i j M W))
    (hVg : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf)) Vg))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) K))
    (hGuard : Derives Γ (substituted w Vg K g f z T Gc vg)) :
    Derives Γ (.equal (H (relationPosition leaf)) vg) := by
  have hb := Derives.conjL (Derives.conjR hd)
  have hRow := Derives.conjL hb
  have hParent := Derives.conjL (Derives.conjR (Derives.conjR hd))
  have hPrefix := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hd)))
  have hQueries := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hd)))
  have hR0 := Derives.conjL (Derives.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hParent))
  have hP := conditions_natural hZ w z T C Refl Pre Gb H U F P N hw hRow
  have hRaw0 := leaf_at w (D 2) S A3 f z T v H N (relationPosition leaf) hQueries
  have hRaw : Derives Γ (substituted w (D 2) S A3 f z T (v (ForcingRelationSource.rawSlot leaf)) (H (relationPosition leaf))) :=
    of_eq (by rw [relation_slot]) hRaw0
  exact ForcingRelationRawFormula.relation_leaf hZ R leaf w z A1 A2 A3 g f T B S (v (ForcingRelationSource.rawSlot leaf)) Gc X i j M W Vg K (H (relationPosition leaf)) vg
    E (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) (quad (U 0) (U 1) (U 2) (N 0)) P D
    hw hz hA1 hA2 hf hSource hPrefix hR0 hP hImages hVg hK hRaw hGuard

end PPAC.Migration.ForcingPreorderLeaves
