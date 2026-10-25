import PPAC.Migration.Internal.StructuralListSpliceTotal
import PPAC.Migration.Internal.StructuralListTraceAppend

/-! One actual coupled-seeded step shares its indices with the original ordered list construction. -/
namespace PPAC.Migration.Internal.PacketTokensBytesRowSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def push {m} (w h u v : Fin m) : Formula m :=
  (Formula.mem h w).conj (.ex
    ((PacketVarintSyntax.canonical w.castSucc h.castSucc (Fin.last m)).conj
      (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) u.castSucc v.castSucc)))

theorem push_rename {m k} (w h u v : Fin m) (ρ : Fin m → Fin k) :
    (push w h u v).rename ρ = push (ρ w) (ρ h) (ρ u) (ρ v) := by
  simp only [push,Formula.rename,PacketVarintSyntax.canonical_rename,StructuralListSpliceSyntax.splice_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_push {m} {Γ : Context m} (w h u v V : Fin m)
    (hc : Derives Γ (PacketVarintSyntax.canonical w h V)) (hs : Derives Γ (StructuralListSpliceSyntax.splice w V u v)) : Derives Γ (push w h u v) := by
  apply Derives.conjI (.conjL (PacketVarintDomain.domain w h V hc))
  apply Derives.exI V
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,PacketVarintSyntax.canonical_rename,StructuralListSpliceSyntax.splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hc hs)

theorem push_input_valid {m} {Γ : Context m} (w h u v : Fin m) (hp : Derives Γ (push w h u v)) :
    Derives Γ (StructuralListTraceSyntax.valid w u) := by
  let R := (PacketVarintSyntax.canonical w.castSucc h.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) u.castSucc v.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR hp)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using StructuralListSplice.tail_valid _ _ _ _ (.conjR hR)

theorem push_output_valid {m} {Γ : Context m} (w h u v : Fin m) (hp : Derives Γ (push w h u v)) :
    Derives Γ (StructuralListTraceSyntax.valid w v) := by
  let R := (PacketVarintSyntax.canonical w.castSucc h.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) u.castSucc v.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR hp)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using StructuralListSplice.joined_valid _ _ _ _ (.conjR hR)

theorem push_output_natural {m} {Γ : Context m} (w h u v : Fin m) (hp : Derives Γ (push w h u v)) : Derives Γ (.mem v w) :=
  StructuralListValidity.range w v (push_output_valid w h u v hp)

def existsPush {m} (w h u : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (push w.castSucc h.castSucc u.castSucc (Fin.last m)))

theorem existsPush_rename {m k} (w h u : Fin m) (ρ : Fin m → Fin k) :
    (existsPush w h u).rename ρ = existsPush (ρ w) (ρ h) (ρ u) := by
  simp only [existsPush,Formula.rename,push_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem splice_prefix {m} {Γ : Context m} (w C D u v : Fin m) (he : Derives Γ (.equal C D))
    (hs : Derives Γ (StructuralListSpliceSyntax.splice w C u v)) : Derives Γ (StructuralListSpliceSyntax.splice w D u v) := by
  let P := StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) u.castSucc v.castSucc
  have h0 : P.instantiate C = StructuralListSpliceSyntax.splice w C u v := by simp only [P,Formula.instantiate,StructuralListSpliceSyntax.splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate D = StructuralListSpliceSyntax.splice w D u v := by simp only [P,Formula.instantiate,StructuralListSpliceSyntax.splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem push_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h u a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (push w h u a)) (hb : Derives Γ (push w h u b)) : Derives Γ (.equal a b) := by
  let R := (PacketVarintSyntax.canonical w.castSucc h.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) u.castSucc a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR ha)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb1 := of_eq (push_rename w h u b Fin.castSucc) (under hb R)
  let S := (PacketVarintSyntax.canonical w.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))).conj (StructuralListSpliceSyntax.splice w.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc b.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (.conjR hb1)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) S
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) S)
  have hcA := of_eq (PacketVarintSyntax.canonical_rename w.castSucc h.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hsA := of_eq (StructuralListSpliceSyntax.splice_rename w.castSucc (Fin.last m) u.castSucc a.castSucc Fin.castSucc) (under (.conjR hR) S)
  have heq := PacketVarintExecutionLiterals.list_unique hZ2 _ _ _ _ hw2 hcA (.conjL hS)
  exact StructuralListSpliceTotal.unique hZ2 _ _ _ _ _ hw2 (splice_prefix _ _ _ _ _ heq hsA) (.conjR hS)

theorem push_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h u : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hu : Derives Γ (StructuralListTraceSyntax.valid w u)) : Derives Γ (existsPush w h u) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (PacketVarintSyntax.canonical w.castSucc h.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketVarintExecutionLiterals.exists_list hZ w h hw hh)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hu1 := of_eq (StructuralListTraceSyntax.valid_rename w u Fin.castSucc) (under hu R)
  have hV := Derives.conjL (.conjR (PacketVarintDomain.domain _ _ _ (.conjR hR)))
  let S := StructuralListSpliceTotalSyntax.fiberBody w.castSucc (Fin.last m) u.castSucc
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (StructuralListSpliceTotal.exists_unique hZ1 _ _ _ hw1 hV hu1)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hc2 := of_eq (PacketVarintSyntax.canonical_rename w.castSucc h.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) S)
  have hPush := intro_push w.castSucc.castSucc h.castSucc.castSucc u.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hc2 (.conjR (.conjL hS))
  have hout : Derives Ξ (existsPush w.castSucc.castSucc h.castSucc.castSucc u.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL (.conjL hS)) hPush)
  simpa only [Formula.raise,existsPush_rename] using hout

def six {m} (j h x y u v : Fin m) : Fin 6 → Fin m := Fin.cases j (Fin.cases h (Fin.cases x (Fin.cases y (Fin.cases u (Fin.cases v Fin.elim0)))))

def rowAt {m} (w f g i j h x y u v : Fin m) : Formula m :=
  (successor j i).conj ((edge f i x).conj ((edge f j y).conj
    ((StructuralListSyntax.consCode w h x y).conj ((edge g i u).conj
      ((edge g j v).conj (PacketTokensBytesRowSyntax.push w h u v))))))

def rowBody {m} (w f g i : Fin m) : Formula (m+6) :=
  rowAt (old 6 w) (old 6 f) (old 6 g) (old 6 i)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def row {m} (w f g i : Fin m) : Formula m := existsMany 6 (rowBody w f g i)

def links {m} (w l f g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (row w.castSucc f.castSucc g.castSucc (Fin.last m)))

theorem rowAt_rename {m k} (w f g i j h x y u v : Fin m) (ρ : Fin m → Fin k) :
    (rowAt w f g i j h x y u v).rename ρ = rowAt (ρ w) (ρ f) (ρ g) (ρ i) (ρ j) (ρ h) (ρ x) (ρ y) (ρ u) (ρ v) := by
  simp only [rowAt,Formula.rename,successor_rename,edge_rename,StructuralListSyntax.consCode_rename,PacketTokensBytesRowSyntax.push_rename]

theorem rowBody_lift {m k} (w f g i : Fin m) (ρ : Fin m → Fin k) :
    (rowBody w f g i).rename (lift 6 ρ) = rowBody (ρ w) (ρ f) (ρ g) (ρ i) := by
  simp only [rowBody,rowAt_rename,lift_old,lift_slot]

theorem row_rename {m k} (w f g i : Fin m) (ρ : Fin m → Fin k) :
    (row w f g i).rename ρ = row (ρ w) (ρ f) (ρ g) (ρ i) := by
  simp only [row,existsMany_rename,rowBody_lift]

theorem links_rename {m k} (w l f g : Fin m) (ρ : Fin m → Fin k) :
    (links w l f g).rename ρ = links (ρ w) (ρ l) (ρ f) (ρ g) := by
  simp only [links,Formula.rename,row_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_row {m} {Γ : Context m} (w f g i j h x y u v : Fin m)
    (hs : Derives Γ (successor j i)) (hx : Derives Γ (edge f i x)) (hy : Derives Γ (edge f j y))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x y)) (hu : Derives Γ (edge g i u)) (hv : Derives Γ (edge g j v))
    (ha : Derives Γ (PacketTokensBytesRowSyntax.push w h u v)) : Derives Γ (row w f g i) := by
  apply HornBinderRules.intro_many 6 (rowBody w f g i) (six j h x y u v)
  exact of_eq (by simp only [rowBody,rowAt_rename,assign_old,assign_slot]; rfl)
    (.conjI hs (.conjI hx (.conjI hy (.conjI hc (.conjI hu (.conjI hv ha))))))

theorem links_at {m} {Γ : Context m} (w l f g i : Fin m) (hl : Derives Γ (links w l f g))
    (hi : Derives Γ (.mem i l)) : Derives Γ (row w f g i) := by
  have h : Derives Γ ((Formula.mem i l).imp (row w f g i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hl)
  exact .impE h hi

theorem empty_links {m} {Γ : Context m} (w z f g : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (links w z f g) := by
  apply Derives.allI
  apply Derives.impI
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz (Formula.mem (Fin.last m) z.castSucc))
  exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokensBytesRowSyntax
