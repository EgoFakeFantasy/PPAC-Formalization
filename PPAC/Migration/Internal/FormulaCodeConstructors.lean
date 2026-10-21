import PPAC.Migration.Internal.FormulaCodeConstructInputs

/-! 全11原构造的合法内部输入实际产生唯一带类型原码；全部存在/唯一量词都在对象层。 -/
namespace PPAC.Migration.Internal.FormulaCodeConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxTermSyntax SyntaxAtomSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeBranchSyntax FormulaCodeConstructSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (contexts w b f)) :
    Derives Γ (law 0 (nullaryTag truth) w (Fin.elim0) b f) := by
  apply law_of_known 0 (nullaryTag truth) w (Fin.elim0) b f (contexts w b f) ht
  let N := constructor 0 (nullaryTag truth) w.castSucc (fun i : Fin 0 => ((Fin.elim0 i) : Fin m).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, zero_map] at hN
  simpa only [Formula.raise, contexts_rename] using FormulaCodeKnownAtomic.nullary_iff hZ1 truth w.castSucc b.castSucc f.castSucc (Fin.last m) hw1 hN

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (contexts w b f)) :
    Derives Γ (typedFiber 0 (nullaryTag truth) w (Fin.elim0) b f) := by
  have hi : Derives Γ (inputs 0 w (Fin.elim0)) := .eqRefl w
  exact FormulaCodeConstruct.actual_fiber hZ 0 (nullaryTag truth) w (Fin.elim0) b f hw hi
    (nullary_law hZ truth w b f hw ht)

theorem member_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (memberTypes w b f s x y)) :
    Derives Γ (law 3 (2) w (three s x y) b f) := by
  apply law_of_known 3 (2) w (three s x y) b f (memberTypes w b f s x y) ht
  let N := constructor 3 (2) w.castSucc (fun i => ((three s x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, three_map] at hN
  simpa only [Formula.raise, memberTypes_rename] using FormulaCodeKnownAtomic.member_iff hZ1 w.castSucc b.castSucc f.castSucc s.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (memberTypes w b f s x y)) :
    Derives Γ (typedFiber 3 (2) w (three s x y) b f) := by
  have hi : Derives Γ (inputs 3 w (three s x y)) := .conjI
    (SyntaxNodeInjective.constructor_range hZ 0 0 w Fin.elim0 s hw (.conjL ht))
    (.conjI (SyntaxTerms.range hZ w b f x hw (.conjL (.conjR ht)))
      (.conjI (SyntaxTerms.range hZ w b f y hw (.conjR (.conjR ht))) (.eqRefl w)))
  exact FormulaCodeConstruct.actual_fiber hZ 3 (2) w (three s x y) b f hw hi
    (member_law hZ w b f s x y hw ht)

theorem equal_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (equalTypes w b f x y)) :
    Derives Γ (law 2 (3) w (two x y) b f) := by
  apply law_of_known 2 (3) w (two x y) b f (equalTypes w b f x y) ht
  let N := constructor 2 (3) w.castSucc (fun i => ((two x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, two_map] at hN
  simpa only [Formula.raise, equalTypes_rename] using FormulaCodeKnownAtomic.equal_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (equalTypes w b f x y)) :
    Derives Γ (typedFiber 2 (3) w (two x y) b f) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (SyntaxTerms.range hZ w b f x hw (.conjL ht))
    (.conjI (SyntaxTerms.range hZ w b f y hw (.conjR ht)) (.eqRefl w))
  exact FormulaCodeConstruct.actual_fiber hZ 2 (3) w (two x y) b f hw hi
    (equal_law hZ w b f x y hw ht)

theorem negation_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes false w b f x)) :
    Derives Γ (law 1 (4) w (fun _ => x) b f) := by
  apply law_of_known 1 (4) w (fun _ => x) b f (singleTypes false w b f x) ht
  let N := constructor 1 (4) w.castSucc (fun i => ((fun _ => x) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  dsimp only [N] at hN
  simpa only [Formula.raise, singleTypes_rename] using FormulaCodeKnownLogical.negation_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc (Fin.last m) hw1 hN

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes false w b f x)) :
    Derives Γ (typedFiber 1 (4) w (fun _ => x) b f) := by
  have hi : Derives Γ (inputs 1 w (fun _ => x)) := .conjI (FormulaCodeConstructInputs.step_natural false w x b f (.conjR ht)) (.eqRefl w)
  exact FormulaCodeConstruct.actual_fiber hZ 1 (4) w (fun _ => x) b f hw hi
    (negation_law hZ w b f x hw ht)

theorem forall_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes true w b f x)) :
    Derives Γ (law 1 (9) w (fun _ => x) b f) := by
  apply law_of_known 1 (9) w (fun _ => x) b f (singleTypes true w b f x) ht
  let N := constructor 1 (9) w.castSucc (fun i => ((fun _ => x) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  dsimp only [N] at hN
  simpa only [Formula.raise, singleTypes_rename] using FormulaCodeKnownLogical.forall_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc (Fin.last m) hw1 hN

theorem universal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes true w b f x)) :
    Derives Γ (typedFiber 1 (9) w (fun _ => x) b f) := by
  have hi : Derives Γ (inputs 1 w (fun _ => x)) := .conjI (FormulaCodeConstructInputs.step_natural true w x b f (.conjR ht)) (.eqRefl w)
  exact FormulaCodeConstruct.actual_fiber hZ 1 (9) w (fun _ => x) b f hw hi
    (forall_law hZ w b f x hw ht)

theorem exists_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes true w b f x)) :
    Derives Γ (law 1 (10) w (fun _ => x) b f) := by
  apply law_of_known 1 (10) w (fun _ => x) b f (singleTypes true w b f x) ht
  let N := constructor 1 (10) w.castSucc (fun i => ((fun _ => x) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  dsimp only [N] at hN
  simpa only [Formula.raise, singleTypes_rename] using FormulaCodeKnownLogical.exists_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc (Fin.last m) hw1 hN

theorem existential {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (singleTypes true w b f x)) :
    Derives Γ (typedFiber 1 (10) w (fun _ => x) b f) := by
  have hi : Derives Γ (inputs 1 w (fun _ => x)) := .conjI (FormulaCodeConstructInputs.step_natural true w x b f (.conjR ht)) (.eqRefl w)
  exact FormulaCodeConstruct.actual_fiber hZ 1 (10) w (fun _ => x) b f hw hi
    (exists_law hZ w b f x hw ht)

theorem binary0_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (law 2 (5) w (two x y) b f) := by
  apply law_of_known 2 (5) w (two x y) b f (binaryTypes w b f x y) ht
  let N := constructor 2 (5) w.castSucc (fun i => ((two x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, two_map] at hN
  simpa only [Formula.raise, binaryTypes_rename] using FormulaCodeKnownLogical.binary0_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem binary0 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (typedFiber 2 (5) w (two x y) b f) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (.conjL (FormulaCodeProperties.guards w x b f (.conjL (.conjR ht))))
    (.conjI (.conjL (FormulaCodeProperties.guards w y b f (.conjR (.conjR ht)))) (.eqRefl w))
  exact FormulaCodeConstruct.actual_fiber hZ 2 (5) w (two x y) b f hw hi
    (binary0_law hZ w b f x y hw ht)

theorem binary1_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (law 2 (6) w (two x y) b f) := by
  apply law_of_known 2 (6) w (two x y) b f (binaryTypes w b f x y) ht
  let N := constructor 2 (6) w.castSucc (fun i => ((two x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, two_map] at hN
  simpa only [Formula.raise, binaryTypes_rename] using FormulaCodeKnownLogical.binary1_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem binary1 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (typedFiber 2 (6) w (two x y) b f) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (.conjL (FormulaCodeProperties.guards w x b f (.conjL (.conjR ht))))
    (.conjI (.conjL (FormulaCodeProperties.guards w y b f (.conjR (.conjR ht)))) (.eqRefl w))
  exact FormulaCodeConstruct.actual_fiber hZ 2 (6) w (two x y) b f hw hi
    (binary1_law hZ w b f x y hw ht)

theorem binary2_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (law 2 (7) w (two x y) b f) := by
  apply law_of_known 2 (7) w (two x y) b f (binaryTypes w b f x y) ht
  let N := constructor 2 (7) w.castSucc (fun i => ((two x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, two_map] at hN
  simpa only [Formula.raise, binaryTypes_rename] using FormulaCodeKnownLogical.binary2_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem binary2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (typedFiber 2 (7) w (two x y) b f) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (.conjL (FormulaCodeProperties.guards w x b f (.conjL (.conjR ht))))
    (.conjI (.conjL (FormulaCodeProperties.guards w y b f (.conjR (.conjR ht)))) (.eqRefl w))
  exact FormulaCodeConstruct.actual_fiber hZ 2 (7) w (two x y) b f hw hi
    (binary2_law hZ w b f x y hw ht)

theorem binary3_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (law 2 (8) w (two x y) b f) := by
  apply law_of_known 2 (8) w (two x y) b f (binaryTypes w b f x y) ht
  let N := constructor 2 (8) w.castSucc (fun i => ((two x y) i).castSucc) (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw N
  have hN0 : Derives Δ N := .hyp (Or.inl rfl)
  have hN := hN0
  simp only [N, two_map] at hN
  simpa only [Formula.raise, binaryTypes_rename] using FormulaCodeKnownLogical.binary3_iff hZ1 w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hN

theorem binary3 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (binaryTypes w b f x y)) :
    Derives Γ (typedFiber 2 (8) w (two x y) b f) := by
  have hi : Derives Γ (inputs 2 w (two x y)) := .conjI (.conjL (FormulaCodeProperties.guards w x b f (.conjL (.conjR ht))))
    (.conjI (.conjL (FormulaCodeProperties.guards w y b f (.conjR (.conjR ht)))) (.eqRefl w))
  exact FormulaCodeConstruct.actual_fiber hZ 2 (8) w (two x y) b f hw hi
    (binary3_law hZ w b f x y hw ht)

def membershipFiber {m} (w b f x y : Fin m) : Formula m := .ex
  ((zeroScalar w.castSucc (Fin.last m)).conj
    (typedFiber 3 2 w.castSucc (three (Fin.last m) x.castSucc y.castSucc) b.castSucc f.castSucc))

theorem membershipFiber_rename {m k} (w b f x y : Fin m) (r : Fin m → Fin k) :
    (membershipFiber w b f x y).rename r = membershipFiber (r w) (r b) (r f) (r x) (r y) := by
  simp only [membershipFiber, Formula.rename, zeroScalar_rename, typedFiber_rename, three_map,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (term w b f x)) (hy : Derives Γ (term w b f y)) :
    Derives Γ (membershipFiber w b f x y) := by
  have he := SyntaxConstructors.exists_constructor hZ 0 0 w Fin.elim0 hw (.eqRefl w)
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (zeroScalar w.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  have heS : Derives Γ (.ex S) := by simpa only [S, zeroScalar, existsConstructor, zero_map] using he
  apply Derives.exE (p := S) heS
  have hZ1 := ZFContext.under hZ S
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hx1 : Derives Δ (term w.castSucc b.castSucc f.castSucc x.castSucc) := by
    simpa only [Formula.raise, term_rename] using under hx S
  have hy1 : Derives Δ (term w.castSucc b.castSucc f.castSucc y.castSucc) := by
    simpa only [Formula.raise, term_rename] using under hy S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hf := member hZ1 w.castSucc b.castSucc f.castSucc (Fin.last m) x.castSucc y.castSucc hw1
    (.conjI (.conjR hS) (.conjI hx1 hy1))
  have hout : Derives Δ (membershipFiber w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, zeroScalar_rename, typedFiber_rename, three_map,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjR hS) hf
  simpa only [Formula.raise, membershipFiber_rename] using hout

end PPAC.Migration.Internal.FormulaCodeConstructors
