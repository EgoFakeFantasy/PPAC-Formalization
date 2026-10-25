import PPAC.Migration.Internal.PacketReaderInitSeed

/-! Initialization is a genuine state-code construction; all initial-code witnesses are eliminated in the reader return relation. -/
namespace PPAC.Migration.Internal.PacketReaderInitSeeded
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInitSyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem run_source {m} {Γ : Context m} (w B z o n r q : Fin m) (he : Derives Γ (.equal n r))
    (hr : Derives Γ (run w B z o n q)) : Derives Γ (run w B z o r q) := by
  let P := run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc
  have h0 : P.instantiate n = run w B z o n q := by simp only [P,Formula.instantiate,run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate r = run w B z o r q := by simp only [P,Formula.instantiate,run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem at_seed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L n q : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (seed w z o L n)) :
    Derives Γ ((seeded w B z o L q).iff (run w B z o n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := seeded w B z o L q
    let R := (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)).conj (run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hs1 := of_eq (seed_rename w z o L n Fin.castSucc) (under (add hs H) R)
    have he := PacketReaderInitSeed.unique hZ1 _ _ _ _ _ _ hw1 (.conjL hR) hs1
    simpa only [Formula.raise,run_rename] using run_source _ _ _ _ _ _ _ he (.conjR hR)
  · apply Derives.impI
    exact intro_seeded w B z o L q n (add hs _) (.hyp (Or.inl rfl))

theorem input_valid {m} {Γ : Context m} (w B z o L q : Fin m) (hr : Derives Γ (seeded w B z o L q)) :
    Derives Γ (StructuralListTraceSyntax.valid w L) := by
  let R := (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)).conj (run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using PacketReaderInitSeed.input_valid _ _ _ _ _ (.conjL hR)

theorem exists_return {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListTraceSyntax.valid w L)) : Derives Γ (existsSeeded w B z o L) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderInitSeed.exists_seed hZ w z o L hw hz ho hL)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := under (StructuralListUnits.member hZ w z o hw hz ho) R
  have he := PacketReaderReturnRunExistence.exists_run hZ1 _ _ _ _ _ hw1 (under hB R) hz1 ho1 (PacketReaderInitSeed.carrier _ _ _ _ _ (.conjR hR))
  let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (run w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) he
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hs2 := of_eq (seed_rename w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) S)
  have hOut := intro_seeded _ _ _ _ _ _ _ hs2 (.conjR hS)
  have hout : Derives Ξ (existsSeeded w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hS) hOut)
  simpa only [Formula.raise,existsSeeded_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L p q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hp : Derives Γ (seeded w B z o L p)) (hq : Derives Γ (seeded w B z o L q)) : Derives Γ (.equal p q) := by
  let R := (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)).conj (run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) p.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hq1 := of_eq (seeded_rename w B z o L q Fin.castSucc) (under hq R)
  have hn := at_seed hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m) q.castSucc hw1 (.conjL hR)
  exact PacketReaderReturnRunUnique.unique hZ1 _ _ _ _ _ _ _ hw1 (under hB R) (.conjR hR) (.impE (.conjL hn) hq1)

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (seeded w B z o L q)) : Derives Γ (.mem q w) := by
  let R := (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)).conj (run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  exact PacketReaderReturnRunUnique.natural hZ1 _ _ _ _ _ _ hw1 (.conjR hR)

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ ((existsSeeded w B z o L).iff (StructuralListTraceSyntax.valid w L)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsSeeded w B z o L
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (seeded w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives (Context.add R (Context.image Formula.raise (Context.add H Γ))) R := .hyp (Or.inl rfl)
    simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using input_valid _ _ _ _ _ _ (.conjR hR)
  · apply Derives.impI
    exact exists_return (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderInitSeeded
