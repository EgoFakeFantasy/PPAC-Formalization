import PPAC.Migration.ForcingPreorderCode
import PPAC.Migration.ForcingTransitiveGuardProof
import PPAC.Migration.ForcingFormulaDiagram

/-! Actual original preorder opening and native instances. The private finite
patterns describe only its fixed three ALL / five IMP outer shape. Leaves,
substitution tables, scopes, terms and proof codes remain internal variables;
no new syntax checker, evaluator, recursion backend or proof kernel is used. -/
namespace PPAC.Migration.ForcingPreorderInstances
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def implications : Nat → {m : Nat} → Fin m → Fin m → Formula m
  | 0, _, _, n => .equal n n
  | k+1, _, w, n => .ex (.ex
      ((SyntaxLogicalSyntax.binaryCode 2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)).conj
        (implications k (old 2 w) (slot 2 1))))

private theorem implications_rename (k : Nat) {m l} (w n : Fin m) (ρ : Fin m → Fin l) :
    (implications k w n).rename ρ = implications k (ρ w) (ρ n) := by
  induction k generalizing m l with
  | zero => rfl
  | succ k ih =>
    change (existsMany 2 ((SyntaxLogicalSyntax.binaryCode 2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)).conj
      (implications k (old 2 w) (slot 2 1)))).rename ρ =
      existsMany 2 ((SyntaxLogicalSyntax.binaryCode 2 (old 2 (ρ w)) (slot 2 0) (slot 2 1) (old 2 (ρ n))).conj
        (implications k (old 2 (ρ w)) (slot 2 1)))
    simp only [existsMany_rename, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, ih, lift_old, lift_slot]


private theorem implications_intro {m} {Γ : Context m} (k : Nat) (w n x y : Fin m)
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w x y n))
    (ht : Derives Γ (implications k w y)) : Derives Γ (implications (k+1) w n) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two x y)
  exact of_eq (by simp only [Formula.rename, SyntaxLogicalSyntax.binaryCode_rename,
    implications_rename, assign_old, assign_slot]; rfl) (.conjI hc ht)

private def allPrefix : Nat → {m : Nat} → Fin m → Fin m → Formula m
  | 0, _, w, n => implications 5 w n
  | k+1, m, w, n => .ex ((SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) n.castSucc).conj
      (allPrefix k w.castSucc (Fin.last m)))

private theorem allPrefix_rename (k : Nat) {m l} (w n : Fin m) (ρ : Fin m → Fin l) :
    (allPrefix k w n).rename ρ = allPrefix k (ρ w) (ρ n) := by
  induction k generalizing m l with
  | zero => exact implications_rename 5 w n ρ
  | succ k ih => simp only [allPrefix, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, ih,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem allPrefix_intro {m} {Γ : Context m} (k : Nat) (w n x : Fin m)
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w x n))
    (ht : Derives Γ (allPrefix k w x)) : Derives Γ (allPrefix (k+1) w n) := by
  apply Derives.exI x
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
    allPrefix_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hc ht)

private theorem implications_transport (k : Nat) : ∀ {m} {Γ : Context m}
    (_hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m),
    Derives Γ (omega w) → Derives Γ (substituted w R S a b c d n q) →
    Derives Γ (implications k w n) → Derives Γ (implications k w q) := by
  induction k with
  | zero => intro m Γ hZ w R S a b c d n q hw hp hs; exact .eqRefl q
  | succ k ih =>
    intro m Γ hZ w R S a b c d n q hw hp hs
    let B : Formula (m+2) :=
      (SyntaxLogicalSyntax.binaryCode 2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)).conj
        (implications k (old 2 w) (slot 2 1))
    let Δ := Context.add B (raisedContext 2 Γ)
    apply HornBinderRules.eliminate_many 2 B _ hs
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 hZ B
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
    have hp2 := of_eq (substituted_rename w R S a b c d n q (old 2)) (HornBinderRules.under_body 2 hp B)
    have he := ForcingFormulaDiagram.binary_output hZ2 2 (old 2 w) (old 2 R) (old 2 S)
      (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (slot 2 0) (slot 2 1) (old 2 q) hw2 (Derives.conjL hB) hp2
    let C := ForcingFormulaDiagram.binaryBody 2 (old 2 w) (old 2 R) (old 2 S)
      (old 2 a) (old 2 b) (old 2 c) (old 2 d) (slot 2 0) (slot 2 1) (old 2 q)
    let Ξ := Context.add C (raisedContext 2 Δ)
    apply HornBinderRules.eliminate_many 2 C _ he
    have hC : Derives Ξ C := .hyp (Or.inl rfl)
    have hZ4 := HornBinderRules.zf_body 2 hZ2 C
    have hw4 := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw2 C)
    have hTail := of_eq (implications_rename k (old 2 w) (slot 2 1) (old 2)) (HornBinderRules.under_body 2 (Derives.conjR hB) C)
    have hQ := ih hZ4 (old 2 (old 2 w)) (old 2 (old 2 R)) (old 2 (old 2 S))
      (old 2 (old 2 a)) (old 2 (old 2 b)) (old 2 (old 2 c)) (old 2 (old 2 d))
      (old 2 (slot 2 1)) (slot 2 1) hw4 (Derives.conjR (Derives.conjR hC)) hTail
    have hout := implications_intro k (old 2 (old 2 w)) (old 2 (old 2 q)) (slot 2 0) (slot 2 1) (Derives.conjL hC) hQ
    exact of_eq (by simp only [implications_rename] <;> rfl) hout

private theorem allPrefix_transport (k : Nat) : ∀ {m} {Γ : Context m}
    (_hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m),
    Derives Γ (omega w) → Derives Γ (substituted w R S a b c d n q) →
    Derives Γ (allPrefix k w n) → Derives Γ (allPrefix k w q) := by
  induction k with
  | zero => exact implications_transport 5
  | succ k ih =>
    intro m Γ hZ w R S a b c d n q hw hp hs
    let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) n.castSucc).conj
      (allPrefix k w.castSucc (Fin.last m))
    let Δ := Context.add E (Context.image Formula.raise Γ)
    apply Derives.exE (p := E) hs
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ E
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
    have hp1 := of_eq (substituted_rename w R S a b c d n q Fin.castSucc) (under hp E)
    have he := ForcingMixedUnary.single_output hZ1 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩))
      w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (Derives.conjL hE) hp1
    let F := (SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc).conj
      (SyntaxMixedFormulaRecursiveSyntax.advanced w.castSucc.castSucc (Fin.last m).castSucc R.castSucc.castSucc S.castSucc.castSucc
        a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add F (Context.image Formula.raise Δ)
    apply Derives.exE (p := F) he
    have hF : Derives Ξ F := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 F
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 F)
    have hTail := of_eq (allPrefix_rename k w.castSucc (Fin.last m) Fin.castSucc) (under (Derives.conjR hE) F)
    have hChild : Derives Ξ (allPrefix k w.castSucc.castSucc (Fin.last (m+1))) := by
      let B := SyntaxMixedFormulaRecursiveSyntax.advancedBody w.castSucc.castSucc (Fin.last m).castSucc
        R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
      let Ω := Context.add B (raisedContext 4 Ξ)
      apply SyntaxMixedFormulaAdvancedOutput.eliminate_advanced w.castSucc.castSucc (Fin.last m).castSucc
        R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) _ (Derives.conjR hF)
      have hB : Derives Ω B := .hyp (Or.inl rfl)
      have hZ6 := HornBinderRules.zf_body 4 hZ2 B
      have hw6 := of_eq (omega_rename w.castSucc.castSucc (old 4)) (HornBinderRules.under_body 4 hw2 B)
      have hTail6 := of_eq (allPrefix_rename k w.castSucc.castSucc (Fin.last m).castSucc (old 4)) (HornBinderRules.under_body 4 hTail B)
      have hout := ih hZ6 (old 4 w.castSucc.castSucc) (slot 4 2) (slot 4 3)
        (slot 4 0) (old 4 b.castSucc.castSucc) (slot 4 1) (old 4 d.castSucc.castSucc)
        (old 4 (Fin.last m).castSucc) (old 4 (Fin.last (m+1))) hw6 (Derives.conjR hB) hTail6
      exact of_eq (by simp only [Formula.raise, allPrefix_rename] <;> rfl) hout
    have hout := allPrefix_intro k w.castSucc.castSucc q.castSucc.castSucc (Fin.last (m+1)) (Derives.conjL hF) hChild
    exact of_eq (by simp only [Formula.raise, allPrefix_rename] <;> rfl) hout

private theorem instantiated_allPrefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w a b A P n q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w a b A P n q))
    (hs : Derives Γ (allPrefix k w n)) : Derives Γ (allPrefix k w q) := by
  let E := SyntaxTopFormulaSyntax.instantiateBody w a b A P n q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hs2 := of_eq (allPrefix_rename k w n (old 2)) (HornBinderRules.under_body 2 hs E)
  have hout := allPrefix_transport k (HornBinderRules.zf_body 2 hZ E) (old 2 w) (slot 2 0) (slot 2 1)
    (old 2 A) (old 2 b) (old 2 a) (old 2 b) (old 2 n) (old 2 q) hw2 (Derives.conjR hE) hs2
  exact of_eq (by simp only [allPrefix_rename] <;> rfl) hout

private def instanceChain : (k : Nat) → {m : Nat} → Fin m → Fin m → Fin m → Fin m → (Fin k → Fin m) → Fin m → Formula m
  | 0, _, w, _, _, _, _, n => implications 5 w n
  | k+1, _, w, z, T, C, P, n => .ex (.ex
      ((SyntaxLogicalSyntax.singleCode 9 (old 2 w) (slot 2 0) (old 2 n)).conj
        ((SyntaxTopFormulaSyntax.instantiated (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 0)) (slot 2 0) (slot 2 1)).conj
          (instanceChain k (old 2 w) (old 2 z) (old 2 T) (old 2 C) (fun i => old 2 (P i.succ)) (slot 2 1)))))

private theorem instanceChain_rename (k : Nat) {m l} (w z T C : Fin m) (P : Fin k → Fin m) (n : Fin m) (ρ : Fin m → Fin l) :
    (instanceChain k w z T C P n).rename ρ = instanceChain k (ρ w) (ρ z) (ρ T) (ρ C) (fun i => ρ (P i)) (ρ n) := by
  induction k generalizing m l with
  | zero => exact implications_rename 5 w n ρ
  | succ k ih =>
    change (existsMany 2 _).rename ρ = existsMany 2 _
    simp only [existsMany_rename, Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
      SyntaxTopFormulaSyntax.instantiated_rename, ih, lift_old, lift_slot]

private theorem instanceChain_intro {m} {Γ : Context m} (k : Nat) (w z T C : Fin m) (P : Fin (k+1) → Fin m) (n F q : Fin m)
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F n))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C (P 0) F q))
    (ht : Derives Γ (instanceChain k w z T C (fun i => P i.succ) q)) :
    Derives Γ (instanceChain (k+1) w z T C P n) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two F q)
  exact of_eq (by simp only [Formula.rename, SyntaxLogicalSyntax.singleCode_rename,
    SyntaxTopFormulaSyntax.instantiated_rename, instanceChain_rename, assign_old, assign_slot]; rfl)
    (.conjI hc (.conjI hi ht))

private theorem instanceChain_exists (k : Nat) : ∀ {m} {Γ : Context m}
    (_hZ : ZFContext.Evidence Γ) (w z T C : Fin m) (P : Fin k → Fin m) (n : Fin m),
    Derives Γ (omega w) → Derives Γ (successor C z) →
    (∀ i, Derives Γ (SyntaxTermSyntax.term w z T (P i))) →
    Derives Γ (formulaCode w n z T) → Derives Γ (allPrefix k w n) →
    Derives Γ (instanceChain k w z T C P n) := by
  induction k with
  | zero => intro m Γ hZ w z T C P n hw hC hP hn hs; exact hs
  | succ k ih =>
    intro m Γ hZ w z T C P n hw hC hP hn hs
    let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) n.castSucc).conj
      (allPrefix k w.castSucc (Fin.last m))
    let Δ := Context.add E (Context.image Formula.raise Γ)
    apply Derives.exE (p := E) hs
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under hZ E
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
    have hC1 := of_eq (successor_rename C z Fin.castSucc) (under hC E)
    have hn1 := of_eq (formulaCode_rename w n z T Fin.castSucc) (under hn E)
    have hP1 : ∀ i, Derives Δ (SyntaxTermSyntax.term w.castSucc z.castSucc T.castSucc (P i).castSucc) :=
      fun i => of_eq (SyntaxTermSyntax.term_rename w z T (P i) Fin.castSucc) (under (hP i) E)
    have hF := Derives.conjR (Derives.impE (Derives.conjL (FormulaCodeKnownLogical.quantified_iff hZ1 true
      w.castSucc z.castSucc T.castSucc (Fin.last m) n.castSucc C.castSucc hw1 (Derives.conjL hE) hC1)) hn1)
    have hex := SyntaxTopFormulaExistence.instantiate_exists hZ1 w.castSucc z.castSucc T.castSucc C.castSucc (P 0).castSucc (Fin.last m)
      hw1 (.conjI (.conjI (hP1 0) hC1) hF)
    let J := SyntaxTopFormulaSyntax.instantiated w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc
      (P 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Ξ := Context.add J (Context.image Formula.raise Δ)
    apply Derives.exE (p := J) hex
    have hJ : Derives Ξ J := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under hZ1 J
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 J)
    have hC2 := of_eq (successor_rename C.castSucc z.castSucc Fin.castSucc) (under hC1 J)
    have hPattern := of_eq (allPrefix_rename k w.castSucc (Fin.last m) Fin.castSucc) (under (Derives.conjR hE) J)
    have hPatternQ := instantiated_allPrefix hZ2 k w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc
      (P 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hJ hPattern
    have hQ := SyntaxTopFormulaTyping.instantiate_target_type w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc
      (P 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hJ
    have hTail := ih hZ2 w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc
      (fun i => (P i.succ).castSucc.castSucc) (Fin.last (m+1)) hw2 hC2
      (fun i => of_eq (SyntaxTermSyntax.term_rename w.castSucc z.castSucc T.castSucc (P i.succ).castSucc Fin.castSucc) (under (hP1 i.succ) J)) hQ hPatternQ
    have hc2 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under (Derives.conjL hE) J)
    have hout := instanceChain_intro k w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc
      (fun i => (P i).castSucc.castSucc) n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc2 hJ hTail
    exact of_eq (by simp only [Formula.raise, instanceChain_rename] <;> rfl) hout

private theorem raw_shape {n m} {Γ : Context m} (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m)
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v)) :
    Derives Γ ((SyntaxLogicalSyntax.binaryCode 0 w (v 1) (v 2) (v 0)).conj (allPrefix 3 w (v 2))) := by
  have c0 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))
  have c1 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))
  have c2 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))
  have c3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))
  have c4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))))
  have c5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))
  have c6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr)))))))))))))))))))))))
  have c7 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))))
  have c8 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hr))))))))))))))))))))))))
  have t0 : Derives Γ (implications 0 w (v 15)) := .eqRefl (v 15)
  have t1 := implications_intro 0 w (v 9) (v 14) (v 15) c8 t0
  have t2 := implications_intro 1 w (v 8) (v 13) (v 9) c7 t1
  have t3 := implications_intro 2 w (v 7) (v 12) (v 8) c6 t2
  have t4 := implications_intro 3 w (v 6) (v 11) (v 7) c5 t3
  have t5 := implications_intro 4 w (v 5) (v 10) (v 6) c4 t4
  have a1 := allPrefix_intro 0 w (v 4) (v 5) c3 t5
  have a2 := allPrefix_intro 1 w (v 3) (v 4) c2 a1
  exact .conjI c0 (allPrefix_intro 2 w (v 2) (v 3) c1 a2)

private def nativeCore {m} (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m) : Formula m :=
  (formulaCode w Pre z T).conj ((SyntaxLogicalSyntax.binaryCode 0 w Refl (U 0) Pre).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 0) (U 0)).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 0) (F 0) (U 1)).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 1) (U 1)).conj ((SyntaxTopFormulaSyntax.instantiated w z T C (P 1) (F 1) (U 2)).conj ((SyntaxLogicalSyntax.singleCode 9 w (F 2) (U 2)).conj (SyntaxTopFormulaSyntax.instantiated w z T C (P 2) (F 2) N0)))))))

private theorem nativeCore_rename {m l} (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (nativeCore w z T C Refl Pre N0 U F P).rename ρ = nativeCore (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre) (ρ N0)
      (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) := by
  simp only [nativeCore, Formula.rename, formulaCode_rename, SyntaxLogicalSyntax.binaryCode_rename,
    SyntaxLogicalSyntax.singleCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

private def impFields {m} (w : Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode 2 w (H 0) (N 1) (N 0)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 1) (N 2) (N 1)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 2) (N 3) (N 2)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (H 3) (N 4) (N 3)).conj (SyntaxLogicalSyntax.binaryCode 2 w (H 4) (H 5) (N 4)))))

private theorem impFields_rename {m l} (w : Fin m) (H : Fin 6 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (impFields w H N).rename ρ = impFields (ρ w) (fun i => ρ (H i)) (fun i => ρ (N i)) := by
  simp only [impFields, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename]

def backgroundData {m} (test : Formula 1) (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (ForcingTransitiveGuardProof.row w z T C Refl Pre G H U F P N).conj
    ((InternalProofBackground.implication test w z T (G 0) (H 0)).conj (InternalProofBackground.implication test w z T (G 0) (H 5)))

theorem backgroundData_rename {m l} (test : Formula 1) (w z T C Refl Pre : Fin m) (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (backgroundData test w z T C Refl Pre G H U F P N).rename ρ = backgroundData test (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre)
      (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [backgroundData, Formula.rename, ForcingTransitiveGuardProof.row_rename, InternalProofBackground.implication_rename]

def backgroundBody {m} (test : Formula 1) (w z T C Refl Pre : Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula (m+5) :=
  backgroundData test (old 5 w) (old 5 z) (old 5 T) (old 5 C) (old 5 Refl) (old 5 Pre) (slot 5)
    (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))

def backgroundExists {m} (test : Formula 1) (w z T C Refl Pre : Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  existsMany 5 (backgroundBody test w z T C Refl Pre H U F P N)

theorem backgroundExists_rename {m l} (test : Formula 1) (w z T C Refl Pre : Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (backgroundExists test w z T C Refl Pre H U F P N).rename ρ = backgroundExists test (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre)
      (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [backgroundExists, existsMany_rename, backgroundBody, backgroundData_rename, lift_old, lift_slot]

private theorem finish_background {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre : Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hCore : Derives Γ (nativeCore w z T C Refl Pre (N 0) U F P)) (hImp : Derives Γ (impFields w H N)) :
    Derives Γ (backgroundExists test w z T C Refl Pre H U F P N) := by
  have c0 := (Derives.conjL hCore)
  have c1 := (Derives.conjL (Derives.conjR hCore))
  have c2 := (Derives.conjL (Derives.conjR (Derives.conjR hCore)))
  have c3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hCore))))
  have c4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore)))))
  have c5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore))))))
  have c6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore)))))))
  have c7 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore)))))))
  have d0 := (Derives.conjL hImp)
  have d1 := (Derives.conjL (Derives.conjR hImp))
  have d2 := (Derives.conjL (Derives.conjR (Derives.conjR hImp)))
  have d3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hImp))))
  have d4 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hImp))))
  have tn0 := SyntaxTopFormulaTyping.instantiate_target_type w z T C (P 2) (F 2) (N 0) c7
  have ty0 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 0) (N 1) (N 0) hw d0)) tn0
  have th0 := Derives.conjL (Derives.conjR ty0)
  have tn1 := Derives.conjR (Derives.conjR ty0)
  have ty1 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 1) (N 2) (N 1) hw d1)) tn1
  have th1 := Derives.conjL (Derives.conjR ty1)
  have tn2 := Derives.conjR (Derives.conjR ty1)
  have ty2 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 2) (N 3) (N 2) hw d2)) tn2
  have th2 := Derives.conjL (Derives.conjR ty2)
  have tn3 := Derives.conjR (Derives.conjR ty2)
  have ty3 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 3) (N 4) (N 3) hw d3)) tn3
  have th3 := Derives.conjL (Derives.conjR ty3)
  have tn4 := Derives.conjR (Derives.conjR ty3)
  have ty4 := Derives.impE (Derives.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z T (H 4) (H 5) (N 4) hw d4)) tn4
  have th4 := Derives.conjL (Derives.conjR ty4)
  have tn5 := Derives.conjR (Derives.conjR ty4)
  let Δ0 : Context m := Γ
  have hZ0 := hZ
  have hw0 := hw
  have hz0 := hz
  have hCore0 := hCore
  have hImp0 := hImp
  have hl0 := th3
  have hr0 := th4
  have he0 := FormulaCodeConstruct.exists_of_fiber 2 5 (old 0 w) (SyntaxAtomSyntax.two (old 0 (H 3)) (old 0 (H 4))) (old 0 z) (old 0 T)
    (FormulaCodeConstructors.binary0 hZ0 (old 0 w) (old 0 z) (old 0 T) (old 0 (H 3)) (old 0 (H 4)) hw0
      (.conjI (Derives.conjR (FormulaCodeProperties.guards (old 0 w) (old 0 (H 3)) (old 0 z) (old 0 T) hl0)) (.conjI hl0 hr0)))
  let E0 : Formula (m+1) := (Formula.mem (Fin.last (m+0)) (old 1 w)).conj
    ((SyntaxLogicalSyntax.binaryCode 0 (old 1 w) ((old 0 (H 3))).castSucc ((old 0 (H 4))).castSucc (Fin.last (m+0))).conj
      (formulaCode (old 1 w) (Fin.last (m+0)) (old 1 z) (old 1 T)))
  let Δ1 := Context.add E0 (Context.image Formula.raise Δ0)
  apply Derives.exE (p := E0) he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have tg0 := Derives.conjR (Derives.conjR hE0)
  have hZ1 := ZFContext.under hZ0 E0
  have hw1 : Derives Δ1 (omega (old 1 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw0 E0)
  have hz1 : Derives Δ1 (empty (old 1 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under hz0 E0)
  have hCore1 := of_eq (nativeCore_rename (old 0 w) (old 0 z) (old 0 T) (old 0 C) (old 0 Refl) (old 0 Pre) (old 0 (N 0))
    (fun j => (old 0 (U j))) (fun j => (old 0 (F j))) (fun j => (old 0 (P j))) Fin.castSucc) (under hCore0 E0)
  have hImp1 := of_eq (impFields_rename (old 0 w) (fun j => (old 0 (H j))) (fun j => (old 0 (N j))) Fin.castSucc) (under hImp0 E0)
  have hl1 : Derives Δ1 (formulaCode (old 1 w) (old 1 (H 2)) (old 1 z) (old 1 T)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under th2 E0)
  have hr1 := tg0
  have he1 := FormulaCodeConstruct.exists_of_fiber 2 5 (old 1 w) (SyntaxAtomSyntax.two (old 1 (H 2)) (Fin.last (m+0))) (old 1 z) (old 1 T)
    (FormulaCodeConstructors.binary0 hZ1 (old 1 w) (old 1 z) (old 1 T) (old 1 (H 2)) (Fin.last (m+0)) hw1
      (.conjI (Derives.conjR (FormulaCodeProperties.guards (old 1 w) (old 1 (H 2)) (old 1 z) (old 1 T) hl1)) (.conjI hl1 hr1)))
  let E1 : Formula (m+2) := (Formula.mem (Fin.last (m+1)) (old 2 w)).conj
    ((SyntaxLogicalSyntax.binaryCode 0 (old 2 w) ((old 1 (H 2))).castSucc ((Fin.last (m+0))).castSucc (Fin.last (m+1))).conj
      (formulaCode (old 2 w) (Fin.last (m+1)) (old 2 z) (old 2 T)))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have tg1 := Derives.conjR (Derives.conjR hE1)
  have hZ2 := ZFContext.under hZ1 E1
  have hw2 : Derives Δ2 (omega (old 2 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw1 E1)
  have hz2 : Derives Δ2 (empty (old 2 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under hz1 E1)
  have hCore2 := of_eq (nativeCore_rename (old 1 w) (old 1 z) (old 1 T) (old 1 C) (old 1 Refl) (old 1 Pre) (old 1 (N 0))
    (fun j => (old 1 (U j))) (fun j => (old 1 (F j))) (fun j => (old 1 (P j))) Fin.castSucc) (under hCore1 E1)
  have hImp2 := of_eq (impFields_rename (old 1 w) (fun j => (old 1 (H j))) (fun j => (old 1 (N j))) Fin.castSucc) (under hImp1 E1)
  have hl2 : Derives Δ2 (formulaCode (old 2 w) (old 2 (H 1)) (old 2 z) (old 2 T)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under th1 E0) E1)
  have hr2 := tg1
  have he2 := FormulaCodeConstruct.exists_of_fiber 2 5 (old 2 w) (SyntaxAtomSyntax.two (old 2 (H 1)) (Fin.last (m+1))) (old 2 z) (old 2 T)
    (FormulaCodeConstructors.binary0 hZ2 (old 2 w) (old 2 z) (old 2 T) (old 2 (H 1)) (Fin.last (m+1)) hw2
      (.conjI (Derives.conjR (FormulaCodeProperties.guards (old 2 w) (old 2 (H 1)) (old 2 z) (old 2 T) hl2)) (.conjI hl2 hr2)))
  let E2 : Formula (m+3) := (Formula.mem (Fin.last (m+2)) (old 3 w)).conj
    ((SyntaxLogicalSyntax.binaryCode 0 (old 3 w) ((old 2 (H 1))).castSucc ((Fin.last (m+1))).castSucc (Fin.last (m+2))).conj
      (formulaCode (old 3 w) (Fin.last (m+2)) (old 3 z) (old 3 T)))
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have tg2 := Derives.conjR (Derives.conjR hE2)
  have hZ3 := ZFContext.under hZ2 E2
  have hw3 : Derives Δ3 (omega (old 3 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw2 E2)
  have hz3 : Derives Δ3 (empty (old 3 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under hz2 E2)
  have hCore3 := of_eq (nativeCore_rename (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 Refl) (old 2 Pre) (old 2 (N 0))
    (fun j => (old 2 (U j))) (fun j => (old 2 (F j))) (fun j => (old 2 (P j))) Fin.castSucc) (under hCore2 E2)
  have hImp3 := of_eq (impFields_rename (old 2 w) (fun j => (old 2 (H j))) (fun j => (old 2 (N j))) Fin.castSucc) (under hImp2 E2)
  have hl3 : Derives Δ3 (formulaCode (old 3 w) (old 3 (H 0)) (old 3 z) (old 3 T)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under (under th0 E0) E1) E2)
  have hr3 := tg2
  have he3 := FormulaCodeConstruct.exists_of_fiber 2 5 (old 3 w) (SyntaxAtomSyntax.two (old 3 (H 0)) (Fin.last (m+2))) (old 3 z) (old 3 T)
    (FormulaCodeConstructors.binary0 hZ3 (old 3 w) (old 3 z) (old 3 T) (old 3 (H 0)) (Fin.last (m+2)) hw3
      (.conjI (Derives.conjR (FormulaCodeProperties.guards (old 3 w) (old 3 (H 0)) (old 3 z) (old 3 T) hl3)) (.conjI hl3 hr3)))
  let E3 : Formula (m+4) := (Formula.mem (Fin.last (m+3)) (old 4 w)).conj
    ((SyntaxLogicalSyntax.binaryCode 0 (old 4 w) ((old 3 (H 0))).castSucc ((Fin.last (m+2))).castSucc (Fin.last (m+3))).conj
      (formulaCode (old 4 w) (Fin.last (m+3)) (old 4 z) (old 4 T)))
  let Δ4 := Context.add E3 (Context.image Formula.raise Δ3)
  apply Derives.exE (p := E3) he3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have tg3 := Derives.conjR (Derives.conjR hE3)
  have hZ4 := ZFContext.under hZ3 E3
  have hw4 : Derives Δ4 (omega (old 4 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw3 E3)
  have hz4 : Derives Δ4 (empty (old 4 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under hz3 E3)
  have hCore4 := of_eq (nativeCore_rename (old 3 w) (old 3 z) (old 3 T) (old 3 C) (old 3 Refl) (old 3 Pre) (old 3 (N 0))
    (fun j => (old 3 (U j))) (fun j => (old 3 (F j))) (fun j => (old 3 (P j))) Fin.castSucc) (under hCore3 E3)
  have hImp4 := of_eq (impFields_rename (old 3 w) (fun j => (old 3 (H j))) (fun j => (old 3 (N j))) Fin.castSucc) (under hImp3 E3)
  have hl4 : Derives Δ4 (formulaCode (old 4 w) (old 4 Pre) (old 4 z) (old 4 T)) := of_eq (by simp only [Formula.raise, formulaCode_rename] <;> rfl) (under (under (under (under c0 E0) E1) E2) E3)
  have hr4 := tg3
  have he4 := FormulaCodeConstruct.exists_of_fiber 2 5 (old 4 w) (SyntaxAtomSyntax.two (old 4 Pre) (Fin.last (m+3))) (old 4 z) (old 4 T)
    (FormulaCodeConstructors.binary0 hZ4 (old 4 w) (old 4 z) (old 4 T) (old 4 Pre) (Fin.last (m+3)) hw4
      (.conjI (Derives.conjR (FormulaCodeProperties.guards (old 4 w) (old 4 Pre) (old 4 z) (old 4 T) hl4)) (.conjI hl4 hr4)))
  let E4 : Formula (m+5) := (Formula.mem (Fin.last (m+4)) (old 5 w)).conj
    ((SyntaxLogicalSyntax.binaryCode 0 (old 5 w) ((old 4 Pre)).castSucc ((Fin.last (m+3))).castSucc (Fin.last (m+4))).conj
      (formulaCode (old 5 w) (Fin.last (m+4)) (old 5 z) (old 5 T)))
  let Δ5 := Context.add E4 (Context.image Formula.raise Δ4)
  apply Derives.exE (p := E4) he4
  have hE4 : Derives Δ5 E4 := .hyp (Or.inl rfl)
  have tg4 := Derives.conjR (Derives.conjR hE4)
  have hZ5 := ZFContext.under hZ4 E4
  have hw5 : Derives Δ5 (omega (old 5 w)) := of_eq (by simp only [Formula.raise, omega_rename] <;> rfl) (under hw4 E4)
  have hz5 : Derives Δ5 (empty (old 5 z)) := of_eq (by simp only [Formula.raise, empty_rename] <;> rfl) (under hz4 E4)
  have hCore5 := of_eq (nativeCore_rename (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 Refl) (old 4 Pre) (old 4 (N 0))
    (fun j => (old 4 (U j))) (fun j => (old 4 (F j))) (fun j => (old 4 (P j))) Fin.castSucc) (under hCore4 E4)
  have hImp5 := of_eq (impFields_rename (old 4 w) (fun j => (old 4 (H j))) (fun j => (old 4 (N j))) Fin.castSucc) (under hImp4 E4)
  have cc0 := (Derives.conjL hCore5)
  have cc1 := (Derives.conjL (Derives.conjR hCore5))
  have cc2 := (Derives.conjL (Derives.conjR (Derives.conjR hCore5)))
  have cc3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hCore5))))
  have cc4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore5)))))
  have cc5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore5))))))
  have cc6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore5)))))))
  have cc7 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hCore5)))))))
  have dd0 := (Derives.conjL hImp5)
  have dd1 := (Derives.conjL (Derives.conjR hImp5))
  have dd2 := (Derives.conjL (Derives.conjR (Derives.conjR hImp5)))
  have dd3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hImp5))))
  have dd4 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hImp5))))
  have cg0 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 0 (old 5 w) (old 5 (H 3)) (old 5 (H 4)) (slot 5 0)) :=
    of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (under (under (under (Derives.conjL (Derives.conjR hE0)) E1) E2) E3) E4)
  have cg1 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 0 (old 5 w) (old 5 (H 2)) (slot 5 0) (slot 5 1)) :=
    of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (under (under (Derives.conjL (Derives.conjR hE1)) E2) E3) E4)
  have cg2 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 0 (old 5 w) (old 5 (H 1)) (slot 5 1) (slot 5 2)) :=
    of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (under (Derives.conjL (Derives.conjR hE2)) E3) E4)
  have cg3 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 0 (old 5 w) (old 5 (H 0)) (slot 5 2) (slot 5 3)) :=
    of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (under (Derives.conjL (Derives.conjR hE3)) E4)
  have cg4 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 0 (old 5 w) (old 5 Pre) (slot 5 3) (slot 5 4)) :=
    of_eq (by rfl) (Derives.conjL (Derives.conjR hE4))
  let G : Fin 5 → Fin (m+5) := Fin.cases (slot 5 4) (Fin.cases (slot 5 3) (Fin.cases (slot 5 2) (Fin.cases (slot 5 1) (fun _ => slot 5 0))))
  have hRow : Derives Δ5 (ForcingTransitiveGuardProof.row (old 5 w) (old 5 z) (old 5 T) (old 5 C) (old 5 Refl) (old 5 Pre) G
    (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))) :=
    (.conjI tg4 (.conjI cc1 (.conjI cg4 (.conjI cg3 (.conjI cg2 (.conjI cg1 (.conjI cg0 (.conjI cc2 (.conjI cc3 (.conjI cc4 (.conjI cc5 (.conjI cc6 (.conjI cc7 (.conjI dd0 (.conjI dd1 (.conjI dd2 (.conjI dd3 dd4)))))))))))))))))
  have hp := ForcingTransitiveGuardProof.at_background hZ5 test (old 5 w) (old 5 z) (old 5 T) (old 5 C) (old 5 Refl) (old 5 Pre) G
    (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i)) hw5 hz5 hRow
  have hout : Derives Δ5 (backgroundExists test (old 5 w) (old 5 z) (old 5 T) (old 5 C) (old 5 Refl) (old 5 Pre)
      (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N i))) := by
    apply HornBinderRules.intro_many 5 _ G
    exact of_eq (by simp only [backgroundBody, backgroundData_rename, assign_old, assign_slot]; rfl) (.conjI hRow hp)
  exact of_eq (by simp only [Formula.raise, backgroundExists_rename] <;> rfl) hout

private theorem cases_map {a : Type} {b : Type} {k : Nat} (ρ : a → b) (x : a) (f : Fin k → a) :
    (fun i => ρ (Fin.cases x f i)) = Fin.cases (ρ x) (fun j => ρ (f j)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def matrixBody {m} (test : Formula 1) (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m) : Formula (m+10) :=
  backgroundExists test (old 10 w) (old 10 z) (old 10 T) (old 10 C) (old 10 Refl) (old 10 Pre)
    (Fin.cases (slot 10 0) (Fin.cases (slot 10 2) (Fin.cases (slot 10 4) (Fin.cases (slot 10 6) (Fin.cases (slot 10 8) (fun _ => (slot 10 9))))))) (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i)) (Fin.cases (old 10 N0) (Fin.cases (slot 10 1) (Fin.cases (slot 10 3) (Fin.cases (slot 10 5) (fun _ => (slot 10 7))))))

def matrixExists {m} (test : Formula 1) (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m) : Formula m :=
  existsMany 10 (matrixBody test w z T C Refl Pre N0 U F P)

theorem matrixExists_rename {m l} (test : Formula 1) (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (matrixExists test w z T C Refl Pre N0 U F P).rename ρ = matrixExists test (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre) (ρ N0)
      (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) := by
  simp only [matrixExists, existsMany_rename, matrixBody, backgroundExists_rename, cases_map, lift_old, lift_slot]

private theorem finish_matrix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre N0 : Fin m) (U F P : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hCore : Derives Γ (nativeCore w z T C Refl Pre N0 U F P)) (hs : Derives Γ (implications 5 w N0)) :
    Derives Γ (matrixExists test w z T C Refl Pre N0 U F P) := by
  let Δ0 : Context m := Γ
  have hZ0 := hZ
  have hw0 := hw
  have hz0 := hz
  have hCore0 := hCore
  have hs0 := hs
  let E0 : Formula (m+2) := (SyntaxLogicalSyntax.binaryCode 2 (old 2 w) (slot 2 0) (slot 2 1) ((old 0 N0)).castSucc.castSucc).conj
    (implications 4 (old 2 w) (slot 2 1))
  let Δ1 := Context.add E0 (raisedContext 2 Δ0)
  apply HornBinderRules.eliminate_many 2 E0 _ hs0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hs1 := Derives.conjR hE0
  have hZ1 := HornBinderRules.zf_body 2 hZ0 E0
  have hw1 : Derives Δ1 (omega (old 2 w)) := of_eq (omega_rename (old 0 w) (old 2)) (HornBinderRules.under_body 2 hw0 E0)
  have hz1 : Derives Δ1 (empty (old 2 z)) := of_eq (empty_rename (old 0 z) (old 2)) (HornBinderRules.under_body 2 hz0 E0)
  have hCore1 := of_eq (nativeCore_rename (old 0 w) (old 0 z) (old 0 T) (old 0 C) (old 0 Refl) (old 0 Pre) (old 0 N0)
    (fun j => (old 0 (U j))) (fun j => (old 0 (F j))) (fun j => (old 0 (P j))) (old 2)) (HornBinderRules.under_body 2 hCore0 E0)
  let E1 : Formula (m+4) := (SyntaxLogicalSyntax.binaryCode 2 (old 4 w) (slot 2 0) (slot 2 1) ((Fin.last (m+1))).castSucc.castSucc).conj
    (implications 3 (old 4 w) (slot 2 1))
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ hs1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hs2 := Derives.conjR hE1
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 : Derives Δ2 (omega (old 4 w)) := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hz2 : Derives Δ2 (empty (old 4 z)) := of_eq (empty_rename (old 2 z) (old 2)) (HornBinderRules.under_body 2 hz1 E1)
  have hCore2 := of_eq (nativeCore_rename (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 Refl) (old 2 Pre) (old 2 N0)
    (fun j => (old 2 (U j))) (fun j => (old 2 (F j))) (fun j => (old 2 (P j))) (old 2)) (HornBinderRules.under_body 2 hCore1 E1)
  let E2 : Formula (m+6) := (SyntaxLogicalSyntax.binaryCode 2 (old 6 w) (slot 2 0) (slot 2 1) ((Fin.last (m+3))).castSucc.castSucc).conj
    (implications 2 (old 6 w) (slot 2 1))
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ hs2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hs3 := Derives.conjR hE2
  have hZ3 := HornBinderRules.zf_body 2 hZ2 E2
  have hw3 : Derives Δ3 (omega (old 6 w)) := of_eq (omega_rename (old 4 w) (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hz3 : Derives Δ3 (empty (old 6 z)) := of_eq (empty_rename (old 4 z) (old 2)) (HornBinderRules.under_body 2 hz2 E2)
  have hCore3 := of_eq (nativeCore_rename (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 Refl) (old 4 Pre) (old 4 N0)
    (fun j => (old 4 (U j))) (fun j => (old 4 (F j))) (fun j => (old 4 (P j))) (old 2)) (HornBinderRules.under_body 2 hCore2 E2)
  let E3 : Formula (m+8) := (SyntaxLogicalSyntax.binaryCode 2 (old 8 w) (slot 2 0) (slot 2 1) ((Fin.last (m+5))).castSucc.castSucc).conj
    (implications 1 (old 8 w) (slot 2 1))
  let Δ4 := Context.add E3 (raisedContext 2 Δ3)
  apply HornBinderRules.eliminate_many 2 E3 _ hs3
  have hE3 : Derives Δ4 E3 := .hyp (Or.inl rfl)
  have hs4 := Derives.conjR hE3
  have hZ4 := HornBinderRules.zf_body 2 hZ3 E3
  have hw4 : Derives Δ4 (omega (old 8 w)) := of_eq (omega_rename (old 6 w) (old 2)) (HornBinderRules.under_body 2 hw3 E3)
  have hz4 : Derives Δ4 (empty (old 8 z)) := of_eq (empty_rename (old 6 z) (old 2)) (HornBinderRules.under_body 2 hz3 E3)
  have hCore4 := of_eq (nativeCore_rename (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 Refl) (old 6 Pre) (old 6 N0)
    (fun j => (old 6 (U j))) (fun j => (old 6 (F j))) (fun j => (old 6 (P j))) (old 2)) (HornBinderRules.under_body 2 hCore3 E3)
  let E4 : Formula (m+10) := (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 2 0) (slot 2 1) ((Fin.last (m+7))).castSucc.castSucc).conj
    (implications 0 (old 10 w) (slot 2 1))
  let Δ5 := Context.add E4 (raisedContext 2 Δ4)
  apply HornBinderRules.eliminate_many 2 E4 _ hs4
  have hE4 : Derives Δ5 E4 := .hyp (Or.inl rfl)
  have hs5 := Derives.conjR hE4
  have hZ5 := HornBinderRules.zf_body 2 hZ4 E4
  have hw5 : Derives Δ5 (omega (old 10 w)) := of_eq (omega_rename (old 8 w) (old 2)) (HornBinderRules.under_body 2 hw4 E4)
  have hz5 : Derives Δ5 (empty (old 10 z)) := of_eq (empty_rename (old 8 z) (old 2)) (HornBinderRules.under_body 2 hz4 E4)
  have hCore5 := of_eq (nativeCore_rename (old 8 w) (old 8 z) (old 8 T) (old 8 C) (old 8 Refl) (old 8 Pre) (old 8 N0)
    (fun j => (old 8 (U j))) (fun j => (old 8 (F j))) (fun j => (old 8 (P j))) (old 2)) (HornBinderRules.under_body 2 hCore4 E4)
  have c0 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 10 0) (slot 10 1) (old 10 N0)) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (Derives.conjL hE0) E1) E2) E3) E4)
  have c1 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 10 2) (slot 10 3) (slot 10 1)) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (Derives.conjL hE1) E2) E3) E4)
  have c2 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 10 4) (slot 10 5) (slot 10 3)) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (Derives.conjL hE2) E3) E4)
  have c3 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 10 6) (slot 10 7) (slot 10 5)) := of_eq (by simp only [SyntaxLogicalSyntax.binaryCode_rename] <;> rfl) (HornBinderRules.under_body 2 (Derives.conjL hE3) E4)
  have c4 : Derives Δ5 (SyntaxLogicalSyntax.binaryCode 2 (old 10 w) (slot 10 8) (slot 10 9) (slot 10 7)) := of_eq (by rfl) (Derives.conjL hE4)
  let H : Fin 6 → Fin (m+10) := (Fin.cases (slot 10 0) (Fin.cases (slot 10 2) (Fin.cases (slot 10 4) (Fin.cases (slot 10 6) (Fin.cases (slot 10 8) (fun _ => (slot 10 9)))))))
  let N : Fin 5 → Fin (m+10) := (Fin.cases (old 10 N0) (Fin.cases (slot 10 1) (Fin.cases (slot 10 3) (Fin.cases (slot 10 5) (fun _ => (slot 10 7))))))
  have hImp : Derives Δ5 (impFields (old 10 w) H N) := (.conjI c0 (.conjI c1 (.conjI c2 (.conjI c3 c4))))
  have hp := finish_background hZ5 test (old 10 w) (old 10 z) (old 10 T) (old 10 C) (old 10 Refl) (old 10 Pre) H
    (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i)) N hw5 hz5 hCore5 hImp
  have hout : Derives Δ5 (matrixExists test (old 10 w) (old 10 z) (old 10 T) (old 10 C) (old 10 Refl) (old 10 Pre) (old 10 N0)
      (fun i => old 10 (U i)) (fun i => old 10 (F i)) (fun i => old 10 (P i))) := by
    apply HornBinderRules.intro_many 10 _ (slot 10)
    exact of_eq (by simp only [matrixBody, backgroundExists_rename, cases_map, assign_old, assign_slot]; rfl) hp
  exact of_eq (by simp only [matrixExists_rename] <;> rfl) hout

def instancesBody {m} (test : Formula 1) (w z T C Refl Pre U0 : Fin m) (P : Fin 3 → Fin m) : Formula (m+6) :=
  matrixExists test (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 Refl) (old 6 Pre) (slot 6 5)
    (Fin.cases (old 6 U0) (Fin.cases (slot 6 1) (fun _ => (slot 6 3)))) (Fin.cases (slot 6 0) (Fin.cases (slot 6 2) (fun _ => (slot 6 4)))) (fun i => old 6 (P i))

def instancesProved {m} (test : Formula 1) (w z T C Refl Pre U0 : Fin m) (P : Fin 3 → Fin m) : Formula m :=
  existsMany 6 (instancesBody test w z T C Refl Pre U0 P)

theorem instancesProved_rename {m l} (test : Formula 1) (w z T C Refl Pre U0 : Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (instancesProved test w z T C Refl Pre U0 P).rename ρ = instancesProved test (ρ w) (ρ z) (ρ T) (ρ C) (ρ Refl) (ρ Pre) (ρ U0) (fun i => ρ (P i)) := by
  simp only [instancesProved, existsMany_rename, instancesBody, matrixExists_rename, cases_map, lift_old, lift_slot]

private theorem finish_instances {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z T C Refl Pre U0 : Fin m) (P : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hPre : Derives Γ (formulaCode w Pre z T)) (hRoot : Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w Refl U0 Pre))
    (hs : Derives Γ (instanceChain 3 w z T C P U0)) : Derives Γ (instancesProved test w z T C Refl Pre U0 P) := by
  let Δ0 : Context m := Γ
  have hZ0 := hZ
  have hw0 := hw
  have hz0 := hz
  have hp0 := hPre
  have hr0 := hRoot
  have hs0 := hs
  let E0 : Formula (m+2) := (SyntaxLogicalSyntax.singleCode 9 (old 2 w) (slot 2 0) ((old 0 U0)).castSucc.castSucc).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 (P 0)) (slot 2 0) (slot 2 1)).conj
      (instanceChain 2 (old 2 w) (old 2 z) (old 2 T) (old 2 C) (fun j => (old 2 (P j.succ))) (slot 2 1)))
  let Δ1 := Context.add E0 (raisedContext 2 Δ0)
  apply HornBinderRules.eliminate_many 2 E0 _ hs0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hs1 := Derives.conjR (Derives.conjR hE0)
  have hZ1 := HornBinderRules.zf_body 2 hZ0 E0
  have hw1 : Derives Δ1 (omega (old 2 w)) := of_eq (omega_rename (old 0 w) (old 2)) (HornBinderRules.under_body 2 hw0 E0)
  have hz1 : Derives Δ1 (empty (old 2 z)) := of_eq (empty_rename (old 0 z) (old 2)) (HornBinderRules.under_body 2 hz0 E0)
  have hp1 : Derives Δ1 (formulaCode (old 2 w) (old 2 Pre) (old 2 z) (old 2 T)) := of_eq (formulaCode_rename (old 0 w) (old 0 Pre) (old 0 z) (old 0 T) (old 2)) (HornBinderRules.under_body 2 hp0 E0)
  have hr1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 (old 0 w) (old 0 Refl) (old 0 U0) (old 0 Pre) (old 2)) (HornBinderRules.under_body 2 hr0 E0)
  let E1 : Formula (m+4) := (SyntaxLogicalSyntax.singleCode 9 (old 4 w) (slot 2 0) ((Fin.last (m+1))).castSucc.castSucc).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 4 w) (old 4 z) (old 4 T) (old 4 C) (old 4 (P 1)) (slot 2 0) (slot 2 1)).conj
      (instanceChain 1 (old 4 w) (old 4 z) (old 4 T) (old 4 C) (fun j => (old 4 (P j.succ.succ))) (slot 2 1)))
  let Δ2 := Context.add E1 (raisedContext 2 Δ1)
  apply HornBinderRules.eliminate_many 2 E1 _ hs1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hs2 := Derives.conjR (Derives.conjR hE1)
  have hZ2 := HornBinderRules.zf_body 2 hZ1 E1
  have hw2 : Derives Δ2 (omega (old 4 w)) := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw1 E1)
  have hz2 : Derives Δ2 (empty (old 4 z)) := of_eq (empty_rename (old 2 z) (old 2)) (HornBinderRules.under_body 2 hz1 E1)
  have hp2 : Derives Δ2 (formulaCode (old 4 w) (old 4 Pre) (old 4 z) (old 4 T)) := of_eq (formulaCode_rename (old 2 w) (old 2 Pre) (old 2 z) (old 2 T) (old 2)) (HornBinderRules.under_body 2 hp1 E1)
  have hr2 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 (old 2 w) (old 2 Refl) (old 2 U0) (old 2 Pre) (old 2)) (HornBinderRules.under_body 2 hr1 E1)
  let E2 : Formula (m+6) := (SyntaxLogicalSyntax.singleCode 9 (old 6 w) (slot 2 0) ((Fin.last (m+3))).castSucc.castSucc).conj
    ((SyntaxTopFormulaSyntax.instantiated (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 2)) (slot 2 0) (slot 2 1)).conj
      (instanceChain 0 (old 6 w) (old 6 z) (old 6 T) (old 6 C) (fun j => (old 6 (P j.succ.succ.succ))) (slot 2 1)))
  let Δ3 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ hs2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hs3 := Derives.conjR (Derives.conjR hE2)
  have hZ3 := HornBinderRules.zf_body 2 hZ2 E2
  have hw3 : Derives Δ3 (omega (old 6 w)) := of_eq (omega_rename (old 4 w) (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hz3 : Derives Δ3 (empty (old 6 z)) := of_eq (empty_rename (old 4 z) (old 2)) (HornBinderRules.under_body 2 hz2 E2)
  have hp3 : Derives Δ3 (formulaCode (old 6 w) (old 6 Pre) (old 6 z) (old 6 T)) := of_eq (formulaCode_rename (old 4 w) (old 4 Pre) (old 4 z) (old 4 T) (old 2)) (HornBinderRules.under_body 2 hp2 E2)
  have hr3 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 (old 4 w) (old 4 Refl) (old 4 U0) (old 4 Pre) (old 2)) (HornBinderRules.under_body 2 hr2 E2)
  have c0 : Derives Δ3 (SyntaxLogicalSyntax.singleCode 9 (old 6 w) (slot 6 0) (old 6 U0)) := of_eq (by simp only [SyntaxLogicalSyntax.singleCode_rename] <;> rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (Derives.conjL hE0) E1) E2)
  have d0 : Derives Δ3 (SyntaxTopFormulaSyntax.instantiated (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 0)) (slot 6 0) (slot 6 1)) := of_eq (by simp only [SyntaxTopFormulaSyntax.instantiated_rename] <;> rfl) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 (Derives.conjL (Derives.conjR hE0)) E1) E2)
  have c1 : Derives Δ3 (SyntaxLogicalSyntax.singleCode 9 (old 6 w) (slot 6 2) (slot 6 1)) := of_eq (by simp only [SyntaxLogicalSyntax.singleCode_rename] <;> rfl) (HornBinderRules.under_body 2 (Derives.conjL hE1) E2)
  have d1 : Derives Δ3 (SyntaxTopFormulaSyntax.instantiated (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 1)) (slot 6 2) (slot 6 3)) := of_eq (by simp only [SyntaxTopFormulaSyntax.instantiated_rename] <;> rfl) (HornBinderRules.under_body 2 (Derives.conjL (Derives.conjR hE1)) E2)
  have c2 : Derives Δ3 (SyntaxLogicalSyntax.singleCode 9 (old 6 w) (slot 6 4) (slot 6 3)) := of_eq (by rfl) (Derives.conjL hE2)
  have d2 : Derives Δ3 (SyntaxTopFormulaSyntax.instantiated (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 (P 2)) (slot 6 4) (slot 6 5)) := of_eq (by rfl) (Derives.conjL (Derives.conjR hE2))
  let U : Fin 3 → Fin (m+6) := (Fin.cases (old 6 U0) (Fin.cases (slot 6 1) (fun _ => (slot 6 3))))
  let F : Fin 3 → Fin (m+6) := (Fin.cases (slot 6 0) (Fin.cases (slot 6 2) (fun _ => (slot 6 4))))
  have hCore : Derives Δ3 (nativeCore (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 Refl) (old 6 Pre) (slot 6 5) U F (fun i => old 6 (P i))) :=
    (.conjI hp3 (.conjI hr3 (.conjI c0 (.conjI d0 (.conjI c1 (.conjI d1 (.conjI c2 d2)))))))
  have hp := finish_matrix hZ3 test (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 Refl) (old 6 Pre) (slot 6 5)
    U F (fun i => old 6 (P i)) hw3 hz3 hCore hs3
  have hout : Derives Δ3 (instancesProved test (old 6 w) (old 6 z) (old 6 T) (old 6 C) (old 6 Refl) (old 6 Pre) (old 6 U0) (fun i => old 6 (P i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [instancesBody, matrixExists_rename, cases_map, assign_old, assign_slot]; rfl) hp
  exact of_eq (by simp only [instancesProved_rename] <;> rfl) hout

/-- Exact original parent opening and its actual three native instances. The
raw parent/children are retained, so guard identification can recover each
original child through existing substitution uniqueness. -/
def targetData {m} (test : Formula 1) (w z f T C B S N L M : Fin m) (P : Fin 3 → Fin m) (Pre Refl U : Fin m) : Formula m :=
  (formulaCode w Pre z T).conj ((substituted w B S z f z T N Pre).conj
    ((SyntaxLogicalSyntax.binaryCode 0 w Refl U Pre).conj
      ((substituted w B S z f z T L Refl).conj
        ((substituted w B S z f z T M U).conj ((instanceChain 3 w z T C P U).conj (instancesProved test w z T C Refl Pre U P))))))

theorem targetData_rename {m l} (test : Formula 1) (w z f T C B S N L M : Fin m) (P : Fin 3 → Fin m) (Pre Refl U : Fin m) (ρ : Fin m → Fin l) :
    (targetData test w z f T C B S N L M P Pre Refl U).rename ρ =
      targetData test (ρ w) (ρ z) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ N) (ρ L) (ρ M) (fun i => ρ (P i)) (ρ Pre) (ρ Refl) (ρ U) := by
  simp only [targetData, Formula.rename, formulaCode_rename, substituted_rename,
    SyntaxLogicalSyntax.binaryCode_rename, instanceChain_rename, instancesProved_rename]

def targetBody {m} (test : Formula 1) (w z f T C B S N L M : Fin m) (P : Fin 3 → Fin m) : Formula (m+3) :=
  targetData test (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 C) (old 3 B) (old 3 S)
    (old 3 N) (old 3 L) (old 3 M) (fun i => old 3 (P i)) (slot 3 0) (slot 3 1) (slot 3 2)

def targetExists {m} (test : Formula 1) (w z f T C B S N L M : Fin m) (P : Fin 3 → Fin m) : Formula m :=
  existsMany 3 (targetBody test w z f T C B S N L M P)

theorem targetExists_rename {m l} (test : Formula 1) (w z f T C B S N L M : Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (targetExists test w z f T C B S N L M P).rename ρ = targetExists test (ρ w) (ρ z) (ρ f) (ρ T) (ρ C) (ρ B) (ρ S) (ρ N) (ρ L) (ρ M) (fun i => ρ (P i)) := by
  simp only [targetExists, existsMany_rename, targetBody, targetData_rename test, lift_old, lift_slot]

theorem open_target {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f T C B S : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hC : Derives Γ (successor C z))
    (hP : ∀ i, Derives Γ (SyntaxTermSyntax.term w z T (P i)))
    (hB : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z T B))
    (hS : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z T S))
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v)) :
    Derives Γ (targetExists test w z f T C B S (v 0) (v 1) (v 2) P) := by
  have hShape := raw_shape R w z A1 A2 A3 f v hr
  have hN := Derives.conjR (Derives.conjL hr)
  have he := SyntaxMixedFormulaOutputInduction.actual_exists hZ w B S z f z T (v 0) hw (.conjI hN (.conjI hB hS))
  let E := substituted w.castSucc B.castSucc S.castSucc z.castSucc f.castSucc z.castSucc T.castSucc (v 0).castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hc1 := of_eq (SyntaxLogicalSyntax.binaryCode_rename 0 w (v 1) (v 2) (v 0) Fin.castSucc) (under (Derives.conjL hShape) E)
  have hp1 := of_eq (allPrefix_rename 3 w (v 2) Fin.castSucc) (under (Derives.conjR hShape) E)
  have he1 := ForcingFormulaDiagram.binary_output hZ1 0 w.castSucc B.castSucc S.castSucc z.castSucc f.castSucc z.castSucc T.castSucc
    (v 0).castSucc (v 1).castSucc (v 2).castSucc (Fin.last m) hw1 hc1 hE
  let J := ForcingFormulaDiagram.binaryBody 0 w.castSucc B.castSucc S.castSucc z.castSucc f.castSucc z.castSucc T.castSucc
    (v 1).castSucc (v 2).castSucc (Fin.last m)
  let Ξ := Context.add J (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 J _ he1
  have hJ : Derives Ξ J := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 2 hZ1 J
  have hw3 := of_eq (omega_rename w.castSucc (old 2)) (HornBinderRules.under_body 2 hw1 J)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hz3 := of_eq (empty_rename z.castSucc (old 2)) (HornBinderRules.under_body 2 hz1 J)
  have hC1 := of_eq (successor_rename C z Fin.castSucc) (under hC E)
  have hC3 := of_eq (successor_rename C.castSucc z.castSucc (old 2)) (HornBinderRules.under_body 2 hC1 J)
  have hP3 : ∀ i, Derives Ξ (SyntaxTermSyntax.term (old 3 w) (old 3 z) (old 3 T) (old 3 (P i))) := by
    intro i
    have h1 := of_eq (SyntaxTermSyntax.term_rename w z T (P i) Fin.castSucc) (under (hP i) E)
    exact of_eq (SyntaxTermSyntax.term_rename w.castSucc z.castSucc T.castSucc (P i).castSucc (old 2)) (HornBinderRules.under_body 2 h1 J)
  have hp3 := of_eq (allPrefix_rename 3 w.castSucc (v 2).castSucc (old 2)) (HornBinderRules.under_body 2 hp1 J)
  have hTrans := Derives.conjR (Derives.conjR hJ)
  have hTarget := SyntaxMixedFormulaJudgment.target_type (old 3 w) (old 3 B) (old 3 S) (old 3 z) (old 3 f) (old 3 z) (old 3 T)
    (old 3 (v 2)) (slot 2 1) hTrans
  have hPattern := allPrefix_transport 3 hZ3 (old 3 w) (old 3 B) (old 3 S) (old 3 z) (old 3 f) (old 3 z) (old 3 T)
    (old 3 (v 2)) (slot 2 1) hw3 hTrans hp3
  have hChain := instanceChain_exists 3 hZ3 (old 3 w) (old 3 z) (old 3 T) (old 3 C) (fun i => old 3 (P i))
    (slot 2 1) hw3 hC3 hP3 hTarget hPattern
  have hParent := of_eq (substituted_rename w.castSucc B.castSucc S.castSucc z.castSucc f.castSucc z.castSucc T.castSucc
    (v 0).castSucc (Fin.last m) (old 2)) (HornBinderRules.under_body 2 hE J)
  have hPre := SyntaxMixedFormulaJudgment.target_type (old 3 w) (old 3 B) (old 3 S) (old 3 z) (old 3 f) (old 3 z) (old 3 T)
    (old 3 (v 0)) (old 2 (Fin.last m)) hParent
  have hProof := finish_instances hZ3 test (old 3 w) (old 3 z) (old 3 T) (old 3 C) (slot 2 0) (old 2 (Fin.last m)) (slot 2 1)
    (fun i => old 3 (P i)) hw3 hz3 hPre (Derives.conjL hJ) hChain
  have hout : Derives Ξ (targetExists test (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 C) (old 3 B) (old 3 S)
      (old 3 (v 0)) (old 3 (v 1)) (old 3 (v 2)) (fun i => old 3 (P i))) := by
    apply HornBinderRules.intro_many 3 _ (Fin.cases (old 2 (Fin.last m)) (Fin.cases (slot 2 0) (fun _ => slot 2 1)))
    exact of_eq (by simp only [targetBody, targetData_rename test, assign_old, assign_slot]; rfl)
      (.conjI hPre (.conjI hParent (.conjI (Derives.conjL hJ) (.conjI (Derives.conjL (Derives.conjR hJ)) (.conjI hTrans (.conjI hChain hProof))))))
  exact of_eq (by simp only [Formula.raise, targetExists_rename test] <;> rfl) hout

/-- Empty bound table is itself generated; no opening or instance output is
an input. All source quotation witnesses remain visible in the final result. -/
def opened {m} (test : Formula 1) (w z f T C S N L M : Fin m) (P : Fin 3 → Fin m) : Formula m := .ex
  ((SyntaxForestSyntax.forest 0 w.castSucc Fin.elim0 (Fin.last m)).conj
    (targetExists test w.castSucc z.castSucc f.castSucc T.castSucc C.castSucc (Fin.last m) S.castSucc N.castSucc L.castSucc M.castSucc (fun i => (P i).castSucc)))

theorem opened_rename {m l} (test : Formula 1) (w z f T C S N L M : Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (opened test w z f T C S N L M P).rename ρ = opened test (ρ w) (ρ z) (ρ f) (ρ T) (ρ C) (ρ S) (ρ N) (ρ L) (ρ M) (fun i => ρ (P i)) := by
  simp only [opened, Formula.rename, SyntaxForestSyntax.forest_rename, targetExists_rename test,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, SyntaxAtomSyntax.zero_map]

def producedData {n m} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (ForcingPreorderCode.rawData R w z A1 A2 A3 f v).conj (opened test w z f T C S (v 0) (v 1) (v 2) P)

theorem producedData_rename {n m l} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) (v : Fin 16 → Fin m) (ρ : Fin m → Fin l) :
    (producedData test R w z A1 A2 A3 f T C S P v).rename ρ =
      producedData test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ S) (fun i => ρ (P i)) (fun i => ρ (v i)) := by
  simp only [producedData, Formula.rename, ForcingPreorderCode.rawData_rename, opened_rename test]

def producedBody {n m} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) : Formula (m+16) :=
  producedData test R (old 16 w) (old 16 z) (old 16 A1) (old 16 A2) (old 16 A3) (old 16 f) (old 16 T) (old 16 C) (old 16 S)
    (fun i => old 16 (P i)) (slot 16)

def produced {n m} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) : Formula m :=
  existsMany 16 (producedBody test R w z A1 A2 A3 f T C S P)

theorem produced_rename {n m l} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (produced test R w z A1 A2 A3 f T C S P).rename ρ = produced test R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ T) (ρ C) (ρ S) (fun i => ρ (P i)) := by
  simp only [produced, existsMany_rename, producedBody, producedData_rename test, lift_old, lift_slot]

/-- Produce the original source quotation, actual empty bound table, actual
opening and all three native instances. Only metadata, the actual free term
table and the three legal terms are inputs; none of the output codes are. -/
theorem produce {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m)
    (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hC : Derives Γ (successor C z))
    (hS : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z T S))
    (hP : ∀ i, Derives Γ (SyntaxTermSyntax.term w z T (P i))) :
    Derives Γ (produced test R w z A1 A2 A3 f T C S P) := by
  let B := ForcingPreorderCode.rawBody R w z A1 A2 A3 f
  let Δ := Context.add B (raisedContext 16 Γ)
  apply HornBinderRules.eliminate_many 16 B _ (ForcingPreorderCode.produce hZ R w z A1 A2 A3 f hw h0 h1 h2 h3 hf)
  have hRaw : Derives Δ B := .hyp (Or.inl rfl)
  have hZ16 := HornBinderRules.zf_body 16 hZ B
  have hw16 := of_eq (omega_rename w (old 16)) (HornBinderRules.under_body 16 hw B)
  have hz16 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old 16)) (HornBinderRules.under_body 16 h0 B)
  have hC16 := of_eq (successor_rename C z (old 16)) (HornBinderRules.under_body 16 hC B)
  have hS16 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z T S (old 16)) (HornBinderRules.under_body 16 hS B)
  have hP16 : ∀ i, Derives Δ (SyntaxTermSyntax.term (old 16 w) (old 16 z) (old 16 T) (old 16 (P i))) :=
    fun i => of_eq (SyntaxTermSyntax.term_rename w z T (P i) (old 16)) (HornBinderRules.under_body 16 (hP i) B)
  have he := SyntaxForests.exists_forest hZ16 0 (old 16 w) Fin.elim0 hw16 (.eqRefl (old 16 w))
  let E := (Formula.mem (Fin.last (m+16)) (old 17 w)).conj
    (SyntaxForestSyntax.forest 0 (old 17 w) Fin.elim0 (Fin.last (m+16)))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) he
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hZ17 := ZFContext.under hZ16 E
  have hw17 := of_eq (omega_rename (old 16 w) Fin.castSucc) (under hw16 E)
  have hz17 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 (old 16 z) Fin.castSucc) (under hz16 E)
  have hC17 := of_eq (successor_rename (old 16 C) (old 16 z) Fin.castSucc) (under hC16 E)
  have hS17 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename (old 16 w) (old 16 f) (old 16 z) (old 16 T) (old 16 S) Fin.castSucc) (under hS16 E)
  have hP17 : ∀ i, Derives Ξ (SyntaxTermSyntax.term (old 17 w) (old 17 z) (old 17 T) (old 17 (P i))) :=
    fun i => of_eq (SyntaxTermSyntax.term_rename (old 16 w) (old 16 z) (old 16 T) (old 16 (P i)) Fin.castSucc) (under (hP16 i) E)
  have hRaw17 := of_eq (ForcingPreorderCode.rawData_rename R (old 16 w) (old 16 z) (old 16 A1) (old 16 A2) (old 16 A3) (old 16 f) (slot 16) Fin.castSucc) (under hRaw E)
  have hBound := ForcingAtomicCode.bound_forest_typed hZ17 (old 17 w) (old 17 z) (old 17 z) (old 17 T) (Fin.last (m+16)) Fin.elim0
    hw17 hz17 (Derives.conjL (hP17 0)) (fun i => Fin.elim0 i) (Derives.conjR hE)
  have hTarget := open_target hZ17 test R (old 17 w) (old 17 z) (old 17 A1) (old 17 A2) (old 17 A3) (old 17 f) (old 17 T) (old 17 C)
    (Fin.last (m+16)) (old 17 S) (fun i => old 17 (P i)) (fun i => (slot 16 i).castSucc) hw17 hz17 hC17 hP17 hBound hS17 hRaw17
  have hOpened : Derives Ξ (opened test (old 17 w) (old 17 z) (old 17 f) (old 17 T) (old 17 C) (old 17 S)
      (slot 16 0).castSucc (slot 16 1).castSucc (slot 16 2).castSucc (fun i => old 17 (P i))) := by
    apply Derives.exI (Fin.last (m+16))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxForestSyntax.forest_rename,
      targetExists_rename test, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq, SyntaxAtomSyntax.zero_map])
      (.conjI (Derives.conjR hE) hTarget)
  have hout : Derives Ξ (produced test R (old 17 w) (old 17 z) (old 17 A1) (old 17 A2) (old 17 A3) (old 17 f) (old 17 T) (old 17 C) (old 17 S)
      (fun i => old 17 (P i))) := by
    apply HornBinderRules.intro_many 16 _ (fun i => (slot 16 i).castSucc)
    exact of_eq (by simp only [producedBody, producedData_rename test, assign_old, assign_slot]; rfl) (.conjI hRaw17 hOpened)
  exact of_eq (by simp only [Formula.raise, produced_rename test] <;> rfl) hout

def input {n m} (_R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (n+2) f).conj ((successor C z).conj ((SyntaxMixedImageCodeSyntax.termList w f z T S).conj ((SyntaxTermSyntax.term w z T (P 0)).conj ((SyntaxTermSyntax.term w z T (P 1)).conj ((SyntaxTermSyntax.term w z T (P 2))))))))))))

def sentence {n m} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) : Source.Sentence :=
  ((input R w z A1 A2 A3 f T C S P).imp (produced test R w z A1 A2 A3 f T C S P)).close

theorem kernel_certificate {n m} (test : Formula 1) (R : Source.Formula (n+2)) (w z A1 A2 A3 f T C S : Fin m) (P : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test R w z A1 A2 A3 f T C S P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input R w z A1 A2 A3 f T C S P
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have h0 := (Derives.conjL h)
  have h1 := (Derives.conjL (Derives.conjR h))
  have h2 := (Derives.conjL (Derives.conjR (Derives.conjR h)))
  have h3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))
  have h4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))
  have h5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))
  have h6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))
  have h7 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))
  have h8 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))
  have h9 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))
  have h10 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))
  have hTerms : ∀ i, Derives Γ (SyntaxTermSyntax.term w z T (P i)) := by
    intro i
    refine Fin.cases h8 (fun j => ?_) i
    refine Fin.cases h9 (fun k => ?_) j
    exact Fin.cases h10 (fun r => Fin.elim0 r) k
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) test R w z A1 A2 A3 f T C S P h0 h1 h2 h3 h4 h5 h6 h7 hTerms


end PPAC.Migration.ForcingPreorderInstances
