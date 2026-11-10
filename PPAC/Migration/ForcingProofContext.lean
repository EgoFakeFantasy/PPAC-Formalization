import PPAC.Migration.ForcingPreorderExistential
import PPAC.Migration.ForcingExistTailComparison
import PPAC.Migration.InternalProofUniversal

/-! Actual proof-context layout for original force_mono/ex.
G0=Pre AND(H0 AND(H1 AND(H2 AND(H3 AND H4)))).
Separate the r-local H0/H3 from Extra/Pre/H1/H2/H4 before fresh forall.
All formulas, code constructors and original Root proofs remain internal.
No background/guard truth or expected rearrangement proof is assumed. -/
namespace PPAC.Migration.ForcingProofContext
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxLogicalSyntax (binaryCode binaryCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem imp_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (formulaCode w A z b)) (hb : Derives Γ (formulaCode w B z b)) :
    Derives Γ (FormulaCodeConstructSyntax.typedExists 2 7 w (SyntaxAtomSyntax.two A B) z b) :=
  FormulaCodeConstruct.exists_of_fiber 2 7 w (SyntaxAtomSyntax.two A B) z b
    (FormulaCodeConstructors.binary2 hZ w z b A B hw
      (Derives.conjI (Derives.conjR (FormulaCodeProperties.guards w A z b ha)) (Derives.conjI ha hb)))

/-- Conditional conjunction uses ONLY original rule11, existing implication
composition and SAME-background discharge/S+MP. G is never assumed proved. -/
private theorem join_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A B C D I : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b)) (ha : Derives Γ (formulaCode w A z b))
    (hb : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (binaryCode 0 w A B C))
    (hd : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 7 w (SyntaxAtomSyntax.two B C) D z b))
    (hi : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 7 w (SyntaxAtomSyntax.two A D) I z b))
    (pa : Derives Γ (implication test w z b G A)) (pb : Derives Γ (implication test w z b G B)) :
    Derives Γ (implication test w z b G C) := by
  have pi := InternalProofConjunction.conjunction_axiom hZ test w z b A B C D I hw hz ha hb hc (Derives.conjL hd) (Derives.conjL hi)
  have pad : Derives Γ (implication test w z b A D) := by
    apply Derives.exI I
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.conjI (Derives.conjL hi) pi)
  have pgd := ForcingRelationGuardProof.chain hZ test w z b G A D hw hz hg ha (Derives.conjR hd) pa pad
  exact ForcingNegMemberProof.discharge hZ test w z b G B C D hw hz hg (Derives.conjR hd) (Derives.conjL hd) pb pgd

private theorem join_after_first {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A B C D : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b)) (ha : Derives Γ (formulaCode w A z b))
    (hb : Derives Γ (formulaCode w B z b))
    (hc : Derives Γ (binaryCode 0 w A B C))
    (hd : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 7 w (SyntaxAtomSyntax.two B C) D z b))
    (pa : Derives Γ (implication test w z b G A)) (pb : Derives Γ (implication test w z b G B)) :
    Derives Γ (implication test w z b G C) := by
  have he := imp_exists hZ w z b A D hw ha (Derives.conjR hd)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 w.castSucc (SyntaxAtomSyntax.two A.castSucc D.castSucc) (Fin.last m) z.castSucc b.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := join_at (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc G.castSucc A.castSucc B.castSucc C.castSucc D.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hg E))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under ha E))
    (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hb E))
    (of_eq (binaryCode_rename 0 w A B C Fin.castSucc) (under hc E))
    (of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]) (under hd E))
    (Derives.conjR hE)
    (of_eq (implication_rename test w z b G A Fin.castSucc) (under pa E))
    (of_eq (implication_rename test w z b G B Fin.castSucc) (under pb E))
  exact of_eq (implication_rename test w z b G C Fin.castSucc).symm out

private theorem join {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b G A B C : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (formulaCode w G z b)) (ha : Derives Γ (formulaCode w A z b))
    (hb : Derives Γ (formulaCode w B z b)) (hc : Derives Γ (binaryCode 0 w A B C))
    (pa : Derives Γ (implication test w z b G A)) (pb : Derives Γ (implication test w z b G B)) :
    Derives Γ (implication test w z b G C) := by
  have htC := Derives.impE (Derives.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b A B C hw hc))
    (Derives.conjI (Derives.conjR (FormulaCodeProperties.guards w A z b ha)) (Derives.conjI ha hb))
  have he := imp_exists hZ w z b B C hw hb htC
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (FormulaCodeConstructSyntax.typedAt 2 7 w.castSucc (SyntaxAtomSyntax.two B.castSucc C.castSucc) (Fin.last m) z.castSucc b.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out := join_after_first (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc G.castSucc A.castSucc B.castSucc C.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hg E))
    (of_eq (formulaCode_rename w A z b Fin.castSucc) (under ha E))
    (of_eq (formulaCode_rename w B z b Fin.castSucc) (under hb E))
    (of_eq (binaryCode_rename 0 w A B C Fin.castSucc) (under hc E))
    (Derives.conjR hE)
    (of_eq (implication_rename test w z b G A Fin.castSucc) (under pa E))
    (of_eq (implication_rename test w z b G B Fin.castSucc) (under pb E))
  exact of_eq (implication_rename test w z b G C Fin.castSucc).symm out

/-- The SIX actual original AND constructors: old-r-free global
Extra AND(Pre AND(H1 AND(H2 AND H4))), r-local H0 AND H3,
and their conjunction. No truth/proof of a leaf is an input. -/
def layoutData {m} (w z b Extra Pre : Fin m) (H v : Fin 6 → Fin m) : Formula m :=
  (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two (H 2) (H 4)) (v 0) z b).conj ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two (H 1) (v 0)) (v 1) z b).conj ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two Pre (v 1)) (v 2) z b).conj ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two Extra (v 2)) (v 3) z b).conj ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two (H 0) (H 3)) (v 4) z b).conj ((FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two (v 3) (v 4)) (v 5) z b))))))

theorem layoutData_rename {m l} (w z b Extra Pre : Fin m) (H v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (layoutData w z b Extra Pre H v).rename ρ =
      layoutData (ρ w) (ρ z) (ρ b) (ρ Extra) (ρ Pre) (fun i => ρ (H i)) (fun i => ρ (v i)) := by
  simp only [layoutData, Formula.rename, FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]

private theorem and_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (binaryCode 0 w A B C)) (ht : Derives Γ (formulaCode w C z b)) :
    Derives Γ ((formulaCode w A z b).conj (formulaCode w B z b)) :=
  Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b A B C hw hc)) ht)

private theorem and_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B C : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (binaryCode 0 w A B C))
    (ha : Derives Γ (formulaCode w A z b)) (hb : Derives Γ (formulaCode w B z b)) :
    Derives Γ (formulaCode w C z b) :=
  Derives.impE (Derives.conjR (FormulaCodeKnownLogical.binary0_iff hZ w z b A B C hw hc))
    (Derives.conjI (Derives.conjR (FormulaCodeProperties.guards w A z b ha)) (Derives.conjI ha hb))

/-- Read the SAME original G0/Extra context and actual existential result,
derive canonicalCtx -> oldCtx internally, then transfer the actual Tail proof
and curry only r-local H0/H3. No rearrangement proof or proved guard supplied. -/
theorem at_layout {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hRow : Derives Γ (ForcingTransitiveGuardProof.row w z b C Refl Pre G H U F P N))
    (hCtx : Derives Γ (binaryCode 0 w Extra (G 0) Ctx))
    (hSource : Derives Γ (ForcingPreorderExistential.resultData test w z b Y Ctx Extra (G 0) (H 0) (H 5) Tail Middle))
    (hl : Derives Γ (layoutData w z b Extra Pre H v)) :
    Derives Γ ((implication test w z b (v 5) Tail).conj
      (InternalProofCurry.result test w z b (v 3) (v 4) Tail)) := by
  have hG0 := (Derives.conjL hRow)
  have o0 := (Derives.conjL (Derives.conjR (Derives.conjR hRow)))
  have o1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hRow))))
  have o2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))
  have o3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow))))))
  have o4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hRow)))))))
  have tG0 := and_types hZ w z b Pre (G 1) (G 0) hw o0 hG0
  have hPre := Derives.conjL tG0
  have hG1 := Derives.conjR tG0
  have tG1 := and_types hZ w z b (H 0) (G 2) (G 1) hw o1 hG1
  have hH0 := Derives.conjL tG1
  have hG2 := Derives.conjR tG1
  have tG2 := and_types hZ w z b (H 1) (G 3) (G 2) hw o2 hG2
  have hH1 := Derives.conjL tG2
  have hG3 := Derives.conjR tG2
  have tG3 := and_types hZ w z b (H 2) (G 4) (G 3) hw o3 hG3
  have hH2 := Derives.conjL tG3
  have hG4 := Derives.conjR tG3
  have tG4 := and_types hZ w z b (H 3) (H 4) (G 4) hw o4 hG4
  have hH3 := Derives.conjL tG4
  have hH4 := Derives.conjR tG4
  have hOldCtx := and_type hZ w z b Extra (G 0) Ctx hw hCtx hExtra hG0
  have c0 := Derives.conjL (Derives.conjL hl)
  have t0 := Derives.conjR (Derives.conjL hl)
  have c1 := Derives.conjL (Derives.conjL (Derives.conjR hl))
  have t1 := Derives.conjR (Derives.conjL (Derives.conjR hl))
  have c2 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR hl)))
  have t2 := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR hl)))
  have c3 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hl))))
  have t3 := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hl))))
  have c4 := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl)))))
  have t4 := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl)))))
  have c5 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl)))))
  have t5 := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl)))))
  have pGlobal := ForcingRelationGuardProof.project hZ test false w z b (v 3) (v 4) (v 5) hw hz t3 t4 t5 c5
  have pLocal := ForcingRelationGuardProof.project hZ test true w z b (v 3) (v 4) (v 5) hw hz t3 t4 t5 c5
  have qExtra := ForcingRelationGuardProof.project hZ test false w z b Extra (v 2) (v 3) hw hz hExtra t2 t3 c3
  have pExtra := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 3) Extra hw hz t5 t3 hExtra pGlobal qExtra
  have qV2 := ForcingRelationGuardProof.project hZ test true w z b Extra (v 2) (v 3) hw hz hExtra t2 t3 c3
  have pV2 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 3) (v 2) hw hz t5 t3 t2 pGlobal qV2
  have qPre := ForcingRelationGuardProof.project hZ test false w z b Pre (v 1) (v 2) hw hz hPre t1 t2 c2
  have pPre := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 2) Pre hw hz t5 t2 hPre pV2 qPre
  have qV1 := ForcingRelationGuardProof.project hZ test true w z b Pre (v 1) (v 2) hw hz hPre t1 t2 c2
  have pV1 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 2) (v 1) hw hz t5 t2 t1 pV2 qV1
  have qH1 := ForcingRelationGuardProof.project hZ test false w z b (H 1) (v 0) (v 1) hw hz hH1 t0 t1 c1
  have pH1 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 1) (H 1) hw hz t5 t1 hH1 pV1 qH1
  have qV0 := ForcingRelationGuardProof.project hZ test true w z b (H 1) (v 0) (v 1) hw hz hH1 t0 t1 c1
  have pV0 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 1) (v 0) hw hz t5 t1 t0 pV1 qV0
  have qH2 := ForcingRelationGuardProof.project hZ test false w z b (H 2) (H 4) (v 0) hw hz hH2 hH4 t0 c0
  have pH2 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 0) (H 2) hw hz t5 t0 hH2 pV0 qH2
  have qH4 := ForcingRelationGuardProof.project hZ test true w z b (H 2) (H 4) (v 0) hw hz hH2 hH4 t0 c0
  have pH4 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 0) (H 4) hw hz t5 t0 hH4 pV0 qH4
  have qH0 := ForcingRelationGuardProof.project hZ test false w z b (H 0) (H 3) (v 4) hw hz hH0 hH3 t4 c4
  have pH0 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 4) (H 0) hw hz t5 t4 hH0 pLocal qH0
  have qH3 := ForcingRelationGuardProof.project hZ test true w z b (H 0) (H 3) (v 4) hw hz hH0 hH3 t4 c4
  have pH3 := ForcingRelationGuardProof.chain hZ test w z b (v 5) (v 4) (H 3) hw hz t5 t4 hH3 pLocal qH3
  have pG4 := join hZ test w z b (v 5) (H 3) (H 4) (G 4) hw hz t5 hH3 hH4 o4 pH3 pH4
  have pG3 := join hZ test w z b (v 5) (H 2) (G 4) (G 3) hw hz t5 hH2 hG4 o3 pH2 pG4
  have pG2 := join hZ test w z b (v 5) (H 1) (G 3) (G 2) hw hz t5 hH1 hG3 o2 pH1 pG3
  have pG1 := join hZ test w z b (v 5) (H 0) (G 2) (G 1) hw hz t5 hH0 hG2 o1 pH0 pG2
  have pG0 := join hZ test w z b (v 5) Pre (G 1) (G 0) hw hz t5 hPre hG1 o0 pPre pG1
  have pCtx := join hZ test w z b (v 5) Extra (G 0) Ctx hw hz t5 hExtra hG0 hCtx pExtra pG0
  have hTail := (Derives.conjL (Derives.conjR (Derives.conjR hSource)))
  have pTail := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hSource))))
  have pCanon := ForcingRelationGuardProof.chain hZ test w z b (v 5) Ctx Tail hw hz t5 hOldCtx hTail pCtx pTail
  have hCurried := InternalProofCurry.from_implication hZ test w z b (v 3) (v 4) (v 5) Tail hw hz t3 t4 hTail c5 pCanon
  exact Derives.conjI pCanon hCurried

private structure Leaves {m} (Γ : Context m) (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m) : Prop where
  hw : Derives Γ (omega w)
  extra : Derives Γ (formulaCode w Extra z b)
  pre : Derives Γ (formulaCode w Pre z b)
  guards : ∀ i : Fin 5, Derives Γ (formulaCode w (H i.castSucc) z b)

private theorem Leaves.under {m} {Γ : Context m} {w z b Extra Pre : Fin m} {H : Fin 6 → Fin m}
    (h : Leaves Γ w z b Extra Pre H) (E : Formula (m+1)) :
    Leaves (Context.add E (Context.image Formula.raise Γ)) w.castSucc z.castSucc b.castSucc Extra.castSucc Pre.castSucc (fun i => (H i).castSucc) :=
  ⟨of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.hw E),
   of_eq (formulaCode_rename w Extra z b Fin.castSucc) (SourceLogic.under h.extra E),
   of_eq (formulaCode_rename w Pre z b Fin.castSucc) (SourceLogic.under h.pre E),
   fun i => of_eq (formulaCode_rename w (H i.castSucc) z b Fin.castSucc) (SourceLogic.under (h.guards i) E)⟩

private theorem and_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (formulaCode w A z b)) (hb : Derives Γ (formulaCode w B z b)) :
    Derives Γ (FormulaCodeConstructSyntax.typedExists 2 5 w (SyntaxAtomSyntax.two A B) z b) :=
  FormulaCodeConstruct.exists_of_fiber 2 5 w (SyntaxAtomSyntax.two A B) z b
    (FormulaCodeConstructors.binary0 hZ w z b A B hw
      (Derives.conjI (Derives.conjR (FormulaCodeProperties.guards w A z b ha)) (Derives.conjI ha hb)))

def layoutBody {m} (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m) : Formula (m+6) :=
  layoutData (old 6 w) (old 6 z) (old 6 b) (old 6 Extra) (old 6 Pre) (fun i => old 6 (H i)) (slot 6)

def layoutExists {m} (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m) : Formula m :=
  existsMany 6 (layoutBody w z b Extra Pre H)

theorem layoutExists_rename {m l} (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (layoutExists w z b Extra Pre H).rename ρ =
      layoutExists (ρ w) (ρ z) (ρ b) (ρ Extra) (ρ Pre) (fun i => ρ (H i)) := by
  simp only [layoutExists, existsMany_rename, layoutBody, layoutData_rename, lift_old, lift_slot]

/-- Exactly six calls to the EXISTING original typed AND constructor.
The returned six codes are OBJECT witnesses, not supplied layout answers. -/
private theorem layout_produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m) (h : Leaves Γ w z b Extra Pre H) :
    Derives Γ (layoutExists w z b Extra Pre H) := by
  let h0 := h
  let hZ0 := hZ
  let E0 := (Formula.mem (Fin.last (m+0)) (old 1 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 1 w) (SyntaxAtomSyntax.two ((H 2)).castSucc ((H 4)).castSucc) (Fin.last (m+0)) (old 1 z) (old 1 b))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (and_exists hZ0 w z b (H 2) (H 4) h0.hw (h0.guards 2) (h0.guards 4))
  apply of_eq (layoutExists_rename w z b Extra Pre (fun i => (H i)) Fin.castSucc).symm
  have e0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have u0_1 := Derives.conjR e0
  have h1 := h0.under E0
  have hZ1 := ZFContext.under hZ0 E0
  let E1 := (Formula.mem (Fin.last (m+1)) (old 2 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 2 w) (SyntaxAtomSyntax.two ((old 1 (H 1))).castSucc ((Fin.last (m+0))).castSucc) (Fin.last (m+1)) (old 2 z) (old 2 b))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) (and_exists hZ1 (old 1 w) (old 1 z) (old 1 b) (old 1 (H 1)) (Fin.last (m+0)) h1.hw (h1.guards 1) (Derives.conjR u0_1))
  apply of_eq (layoutExists_rename (old 1 w) (old 1 z) (old 1 b) (old 1 Extra) (old 1 Pre) (fun i => (old 1 (H i))) Fin.castSucc).symm
  have e1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have u1_2 := Derives.conjR e1
  have h2 := h1.under E1
  have hZ2 := ZFContext.under hZ1 E1
  have u0_2 : Derives Δ2 (FormulaCodeConstructSyntax.typedAt 2 5 (old 2 w) (SyntaxAtomSyntax.two (old 2 (H 2)) (old 2 (H 4))) (old 1 (Fin.last (m+0))) (old 2 z) (old 2 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u0_1 E1)
  let E2 := (Formula.mem (Fin.last (m+2)) (old 3 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 3 w) (SyntaxAtomSyntax.two ((old 2 Pre)).castSucc ((Fin.last (m+1))).castSucc) (Fin.last (m+2)) (old 3 z) (old 3 b))
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) (and_exists hZ2 (old 2 w) (old 2 z) (old 2 b) (old 2 Pre) (Fin.last (m+1)) h2.hw h2.pre (Derives.conjR u1_2))
  apply of_eq (layoutExists_rename (old 2 w) (old 2 z) (old 2 b) (old 2 Extra) (old 2 Pre) (fun i => (old 2 (H i))) Fin.castSucc).symm
  have e2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have u2_3 := Derives.conjR e2
  have h3 := h2.under E2
  have hZ3 := ZFContext.under hZ2 E2
  have u0_3 : Derives Δ3 (FormulaCodeConstructSyntax.typedAt 2 5 (old 3 w) (SyntaxAtomSyntax.two (old 3 (H 2)) (old 3 (H 4))) (old 2 (Fin.last (m+0))) (old 3 z) (old 3 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u0_2 E2)
  have u1_3 : Derives Δ3 (FormulaCodeConstructSyntax.typedAt 2 5 (old 3 w) (SyntaxAtomSyntax.two (old 3 (H 1)) (old 2 (Fin.last (m+0)))) (old 1 (Fin.last (m+1))) (old 3 z) (old 3 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u1_2 E2)
  let E3 := (Formula.mem (Fin.last (m+3)) (old 4 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 4 w) (SyntaxAtomSyntax.two ((old 3 Extra)).castSucc ((Fin.last (m+2))).castSucc) (Fin.last (m+3)) (old 4 z) (old 4 b))
  let Δ4 := Context.add E3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := E3) (and_exists hZ3 (old 3 w) (old 3 z) (old 3 b) (old 3 Extra) (Fin.last (m+2)) h3.hw h3.extra (Derives.conjR u2_3))
  apply of_eq (layoutExists_rename (old 3 w) (old 3 z) (old 3 b) (old 3 Extra) (old 3 Pre) (fun i => (old 3 (H i))) Fin.castSucc).symm
  have e3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have u3_4 := Derives.conjR e3
  have h4 := h3.under E3
  have hZ4 := ZFContext.under hZ3 E3
  have u0_4 : Derives Δ4 (FormulaCodeConstructSyntax.typedAt 2 5 (old 4 w) (SyntaxAtomSyntax.two (old 4 (H 2)) (old 4 (H 4))) (old 3 (Fin.last (m+0))) (old 4 z) (old 4 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u0_3 E3)
  have u1_4 : Derives Δ4 (FormulaCodeConstructSyntax.typedAt 2 5 (old 4 w) (SyntaxAtomSyntax.two (old 4 (H 1)) (old 3 (Fin.last (m+0)))) (old 2 (Fin.last (m+1))) (old 4 z) (old 4 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u1_3 E3)
  have u2_4 : Derives Δ4 (FormulaCodeConstructSyntax.typedAt 2 5 (old 4 w) (SyntaxAtomSyntax.two (old 4 Pre) (old 2 (Fin.last (m+1)))) (old 1 (Fin.last (m+2))) (old 4 z) (old 4 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u2_3 E3)
  let E4 := (Formula.mem (Fin.last (m+4)) (old 5 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 5 w) (SyntaxAtomSyntax.two ((old 4 (H 0))).castSucc ((old 4 (H 3))).castSucc) (Fin.last (m+4)) (old 5 z) (old 5 b))
  let Δ5 := Context.add E4 (Context.image Formula.raise Δ4)
  apply Derives.exE (p := E4) (and_exists hZ4 (old 4 w) (old 4 z) (old 4 b) (old 4 (H 0)) (old 4 (H 3)) h4.hw (h4.guards 0) (h4.guards 3))
  apply of_eq (layoutExists_rename (old 4 w) (old 4 z) (old 4 b) (old 4 Extra) (old 4 Pre) (fun i => (old 4 (H i))) Fin.castSucc).symm
  have e4 : Derives Δ5 E4 := .hyp (Or.inl rfl)
  have u4_5 := Derives.conjR e4
  have h5 := h4.under E4
  have hZ5 := ZFContext.under hZ4 E4
  have u0_5 : Derives Δ5 (FormulaCodeConstructSyntax.typedAt 2 5 (old 5 w) (SyntaxAtomSyntax.two (old 5 (H 2)) (old 5 (H 4))) (old 4 (Fin.last (m+0))) (old 5 z) (old 5 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u0_4 E4)
  have u1_5 : Derives Δ5 (FormulaCodeConstructSyntax.typedAt 2 5 (old 5 w) (SyntaxAtomSyntax.two (old 5 (H 1)) (old 4 (Fin.last (m+0)))) (old 3 (Fin.last (m+1))) (old 5 z) (old 5 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u1_4 E4)
  have u2_5 : Derives Δ5 (FormulaCodeConstructSyntax.typedAt 2 5 (old 5 w) (SyntaxAtomSyntax.two (old 5 Pre) (old 3 (Fin.last (m+1)))) (old 2 (Fin.last (m+2))) (old 5 z) (old 5 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u2_4 E4)
  have u3_5 : Derives Δ5 (FormulaCodeConstructSyntax.typedAt 2 5 (old 5 w) (SyntaxAtomSyntax.two (old 5 Extra) (old 2 (Fin.last (m+2)))) (old 1 (Fin.last (m+3))) (old 5 z) (old 5 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u3_4 E4)
  let E5 := (Formula.mem (Fin.last (m+5)) (old 6 w)).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two ((old 1 (Fin.last (m+3)))).castSucc ((Fin.last (m+4))).castSucc) (Fin.last (m+5)) (old 6 z) (old 6 b))
  let Δ6 := Context.add E5 (Context.image Formula.raise Δ5)
  apply Derives.exE (p := E5) (and_exists hZ5 (old 5 w) (old 5 z) (old 5 b) (old 1 (Fin.last (m+3))) (Fin.last (m+4)) h5.hw (Derives.conjR u3_5) (Derives.conjR u4_5))
  apply of_eq (layoutExists_rename (old 5 w) (old 5 z) (old 5 b) (old 5 Extra) (old 5 Pre) (fun i => (old 5 (H i))) Fin.castSucc).symm
  have e5 : Derives Δ6 E5 := .hyp (Or.inl rfl)
  have u5_6 := Derives.conjR e5
  have u0_6 : Derives Δ6 (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two (old 6 (H 2)) (old 6 (H 4))) (old 5 (Fin.last (m+0))) (old 6 z) (old 6 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u0_5 E5)
  have u1_6 : Derives Δ6 (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two (old 6 (H 1)) (old 5 (Fin.last (m+0)))) (old 4 (Fin.last (m+1))) (old 6 z) (old 6 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u1_5 E5)
  have u2_6 : Derives Δ6 (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two (old 6 Pre) (old 4 (Fin.last (m+1)))) (old 3 (Fin.last (m+2))) (old 6 z) (old 6 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u2_5 E5)
  have u3_6 : Derives Δ6 (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two (old 6 Extra) (old 3 (Fin.last (m+2)))) (old 2 (Fin.last (m+3))) (old 6 z) (old 6 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u3_5 E5)
  have u4_6 : Derives Δ6 (FormulaCodeConstructSyntax.typedAt 2 5 (old 6 w) (SyntaxAtomSyntax.two (old 6 (H 0)) (old 6 (H 3))) (old 1 (Fin.last (m+4))) (old 6 z) (old 6 b)) :=
    of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]; rfl) (SourceLogic.under u4_5 E5)
  let vals : Fin 6 → Fin (m+6) := Fin.cases (old 5 (Fin.last (m+0))) (Fin.cases (old 4 (Fin.last (m+1))) (Fin.cases (old 3 (Fin.last (m+2))) (Fin.cases (old 2 (Fin.last (m+3))) (Fin.cases (old 1 (Fin.last (m+4))) (fun _ => (Fin.last (m+5)))))))
  apply HornBinderRules.intro_many 6 _ vals
  exact of_eq (by simp only [layoutBody, layoutData_rename, assign_old, assign_slot]; rfl)
    (.conjI u0_6 (.conjI u1_6 (.conjI u2_6 (.conjI u3_6 (.conjI u4_6 u5_6)))))

/-- Public typed-input interface to the unchanged original layout producer. -/
theorem layout_from_typed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b Extra Pre : Fin m) (H : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hExtra : Derives Γ (formulaCode w Extra z b))
    (hPre : Derives Γ (formulaCode w Pre z b))
    (hH : ∀ i : Fin 5, Derives Γ (formulaCode w (H i.castSucc) z b)) :
    Derives Γ (layoutExists w z b Extra Pre H) :=
  layout_produce hZ w z b Extra Pre H ⟨hw,hExtra,hPre,hH⟩

def resultData {m} (test : Formula 1) (w z b Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Formula m :=
  (layoutData w z b Extra Pre H v).conj
    ((implication test w z b (v 5) Tail).conj
      (InternalProofCurry.result test w z b (v 3) (v 4) Tail))

theorem resultData_rename {m l} (test : Formula 1) (w z b Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m)
    (ρ : Fin m → Fin l) :
    (resultData test w z b Extra Pre Tail H v).rename ρ =
      resultData test (ρ w) (ρ z) (ρ b) (ρ Extra) (ρ Pre) (ρ Tail) (fun i => ρ (H i)) (fun i => ρ (v i)) := by
  simp only [resultData, Formula.rename, layoutData_rename, implication_rename, InternalProofCurry.result_rename]

private def resultBody {m} (test : Formula 1) (w z b Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) : Formula (m+6) :=
  resultData test (old 6 w) (old 6 z) (old 6 b) (old 6 Extra) (old 6 Pre) (old 6 Tail) (fun i => old 6 (H i)) (slot 6)

def result {m} (test : Formula 1) (w z b Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) : Formula m :=
  existsMany 6 (resultBody test w z b Extra Pre Tail H)

theorem result_rename {m l} (test : Formula 1) (w z b Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (result test w z b Extra Pre Tail H).rename ρ =
      result test (ρ w) (ρ z) (ρ b) (ρ Extra) (ρ Pre) (ρ Tail) (fun i => ρ (H i)) := by
  simp only [result, existsMany_rename, resultBody, resultData_rename, lift_old, lift_slot]

def input {m} (test : Formula 1) (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w Extra z b).conj
    ((ForcingTransitiveGuardProof.row w z b C Refl Pre G H U F P N).conj
      ((binaryCode 0 w Extra (G 0) Ctx).conj
        (ForcingPreorderExistential.resultData test w z b Y Ctx Extra (G 0) (H 0) (H 5) Tail Middle)))))

theorem input_rename {m l} (test : Formula 1) (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (input test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N).rename ρ =
      input test (ρ w) (ρ z) (ρ b) (ρ C) (ρ Refl) (ρ Pre) (ρ Extra) (ρ Ctx) (ρ Tail) (ρ Y) (ρ Middle)
        (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [input, Formula.rename, omega_rename, empty_rename, formulaCode_rename,
    ForcingTransitiveGuardProof.row_rename, binaryCode_rename, ForcingPreorderExistential.resultData_rename]

/-- Consume the actual old-context tail proof. Produce ALL six layout
codes, prove rearrangement by original logical rules, and curry the r-local
pair only. No generated formula, expected permutation or proved guard is input. -/
theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hi : Derives Γ (input test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N)) :
    Derives Γ (result test w z b Extra Pre Tail H) := by
  have hw := Derives.conjL hi
  have hExtra := Derives.conjL (.conjR (.conjR hi))
  have hr := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have t0 := and_types hZ w z b Pre (G 1) (G 0) hw
    (.conjL (.conjR (.conjR hr))) (.conjL hr)
  have t1 := and_types hZ w z b (H 0) (G 2) (G 1) hw
    (.conjL (.conjR (.conjR (.conjR hr)))) (.conjR t0)
  have t2 := and_types hZ w z b (H 1) (G 3) (G 2) hw
    (.conjL (.conjR (.conjR (.conjR (.conjR hr))))) (.conjR t1)
  have t3 := and_types hZ w z b (H 2) (G 4) (G 3) hw
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hr)))))) (.conjR t2)
  have t4 := and_types hZ w z b (H 3) (H 4) (G 4) hw
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hr))))))) (.conjR t3)
  have ht : ∀ i : Fin 5, Derives Γ (formulaCode w (H i.castSucc) z b) := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
    · exact .conjL t1
    · exact .conjL t2
    · exact .conjL t3
    · exact .conjL t4
    · exact .conjR t4
  have he := layout_produce hZ w z b Extra Pre H ⟨hw, hExtra, .conjL t0, ht⟩
  let E := layoutBody w z b Extra Pre H
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi6 := of_eq (input_rename test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N (old 6))
    (HornBinderRules.under_body 6 hi E)
  have hp := at_layout (HornBinderRules.zf_body 6 hZ E) test
    (old 6 w) (old 6 z) (old 6 b) (old 6 C) (old 6 Refl) (old 6 Pre) (old 6 Extra)
    (old 6 Ctx) (old 6 Tail) (old 6 Y) (old 6 Middle)
    (fun i => old 6 (G i)) (fun i => old 6 (H i)) (fun i => old 6 (U i))
    (fun i => old 6 (F i)) (fun i => old 6 (P i)) (fun i => old 6 (N i)) (slot 6)
    (.conjL hi6) (.conjL (.conjR hi6)) (.conjL (.conjR (.conjR hi6)))
    (.conjL (.conjR (.conjR (.conjR hi6))))
    (.conjL (.conjR (.conjR (.conjR (.conjR hi6)))))
    (.conjR (.conjR (.conjR (.conjR (.conjR hi6))))) hE
  have ho : Derives Δ (result test (old 6 w) (old 6 z) (old 6 b) (old 6 Extra) (old 6 Pre) (old 6 Tail)
      (fun i => old 6 (H i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [resultBody, resultData_rename, assign_old, assign_slot]; rfl) (.conjI hE hp)
  exact of_eq (result_rename test w z b Extra Pre Tail H (old 6)).symm ho

def sentence {m} (test : Formula 1) (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((input test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N).imp
    (result test w z b Extra Pre Tail H)).close

theorem kernel_certificate {m} (test : Formula 1) (w z b C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let B := input test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N
  let Γ := Context.add B (Source.SetLanguage.ZF.at m)
  have hB : Derives Γ B := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) B) test w z b C Refl Pre Extra Ctx Tail Y Middle G H U F P N hB

/-- Consume the FULL raw-tail independence theorem on the actual two
executions, then transport the generated canonical-context proof to Tail1.
All trace, common-head and canonical operation witnesses are generated by the
existing raw comparison; none is added as a caller's equality premise. -/
theorem from_queries {k m} {Γ : Context m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 C0 Refl Pre Extra Ctx Y Middle : Fin m) (s : Fin 9 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (hZ : ZFContext.Evidence Γ)
    (hRaw : Derives Γ (ForcingExistTailComparison.rawInput Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 s))
    (hi : Derives Γ (input test w z b C0 Refl Pre Extra Ctx Tail Y Middle G H U F P N)) :
    Derives Γ (result test w z b Extra Pre Tail1 H) := by
  have hp := derive hZ test w z b C0 Refl Pre Extra Ctx Tail Y Middle G H U F P N hi
  have he := ForcingExistTailComparison.from_queries hZ Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 s hRaw
  let E := result test w.castSucc z.castSucc b.castSucc Extra.castSucc Pre.castSucc (Fin.last m) (fun i => (H i).castSucc)
  exact of_eq (by simp only [E, Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst E he
      (of_eq (by simp only [E, Formula.instantiate, result_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp))

def rawSentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 C0 Refl Pre Extra Ctx Y Middle : Fin m) (s : Fin 9 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  (((ForcingExistTailComparison.rawInput Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 s).conj (input test w z b C0 Refl Pre Extra Ctx Tail Y Middle G H U F P N)).imp (result test w z b Extra Pre Tail1 H)).close

theorem raw_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 C0 Refl Pre Extra Ctx Y Middle : Fin m) (s : Fin 9 → Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (rawSentence test Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 C0 Refl Pre Extra Ctx Y Middle s G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (ForcingExistTailComparison.rawInput Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 s).conj (input test w z b C0 Refl Pre Extra Ctx Tail Y Middle G H U F P N)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact from_queries test Reln Dom w z a A B C f b R D Q Base I j p q x Child S Tail S1 Tail1 C0 Refl Pre Extra Ctx Y Middle s G H U F P N
    (ZFContext.add (ZFContext.source_ZF m) E) (.conjL hE) (.conjR hE)

end PPAC.Migration.ForcingProofContext
