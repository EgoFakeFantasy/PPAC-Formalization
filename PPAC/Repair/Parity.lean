/-
PPAC/Repair/Parity.lean — Batch 3, countable-support collapse.

Formalizes §3–§4 of `定向枚举截面修复与完美集障碍_核查.md`: the countable-
support partial-section forcing `P_cnt` (conditions = countable partial
sections of `q : A → B`) projects to the countable binary forcing
`Fn_≤ω(I, 2)` along the fixed old well-ordered real family `b : I → B` with
parity bits, and the generic binary function's countable-block decoder
covers all of `2^Nat` — relationally: `R_old` becomes a surjective image of
the ordinal-like index `I`, hence internally well-orderable.

BOUNDARY: the block/parity data (`blk`, `bit`, `codeBit`, `binv`) and the
uncountability content `block_fresh` (no countable family of `B`-points
meets every block's `b`-image — the host rendition of "I is as large as
ω₁ against countable conditions") are interface hypotheses: the ZF/ordinal
adapter is not formalized in this batch. The collapse is relational; the
internal block-decoder is a function by union functionality, and its
well-ordering transport happens inside ZF (Replacement), listed as a
remaining bridge.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import PPAC.Repair.Projection

namespace PPAC.Repair

/-! ## Interfaces -/

/-- Parity-bit coding along the fixed old family `b : I → B`: `bit ξ a`
reads the bit of a section value at `ξ`, `codeBit ξ v` realizes bit `v`
inside `q⁻¹(b ξ)`, and `binv` decodes base points (old data). -/
structure BitCoding (A B : Type) (q : A → B) (I : Type) where
  b : I → B
  b_inj : Function.Injective b
  pt : I
  bit : I → A → Bool
  codeBit : I → Bool → A
  codeBit_fiber : ∀ ξ v, q (codeBit ξ v) = b ξ
  codeBit_bit : ∀ ξ v, bit ξ (codeBit ξ v) = v
  binv : B → Option I
  binv_self : ∀ ξ, binv (b ξ) = some ξ

/-- Disjoint countable blocks inside `I`, with the uncountability content:
no countable family of `B`-points meets every block's `b`-image. -/
structure BlockCoding {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I) where
  blk : I → Nat → I
  blk_inj : ∀ α α' n n', blk α n = blk α' n' → α = α' ∧ n = n'
  block_fresh : ∀ (D : Type) (_ : Countable D) (u : D → B),
    ∃ α₀, ∀ n d, u d ≠ BC.b (blk α₀ n)

/-- The generic union of a directed family of countable sections. -/
def jrelCnt {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    (G : SecCnt B A q → Prop) (bb : B) (a : A) : Prop :=
  ∃ p : SecCnt B A q, G p ∧ p.rel bb a

/-! ## The relational projection -/

/-- The projected countable binary function: `ξ ↦ bit ξ (p(b ξ))`. -/
def projCnt {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    (p : SecCnt B A q) : CntPartFun I Bool := by
  refine ⟨fun ξ v => ∃ a, p.rel (BC.b ξ) a ∧ BC.bit ξ a = v, ?_, ?_⟩
  · intro ξ x x' h₁ h₂
    cases h₁ with
    | intro a ha =>
      cases h₂ with
      | intro a' ha' =>
        have h : a = a' := p.funi (BC.b ξ) a a' ha.1 ha'.1
        rw [← ha.2, ← ha'.2, h]
  · cases p.cnt with
    | intro c hcov =>
      refine ⟨{ D := c.D, hD := c.hD, w := fun d => Option.getD (BC.binv (c.w d)) BC.pt }, ?_⟩
      intro ξ x hx
      cases hx with
      | intro a ha =>
        cases hcov (BC.b ξ) a ha.1 with
        | intro d hd =>
          refine ⟨d, ?_⟩
          have hbinv : BC.binv (c.w d) = some ξ := by rw [hd]; exact BC.binv_self ξ
          show Option.getD (BC.binv (c.w d)) BC.pt = ξ
          rw [hbinv]
          rfl

/-- The projection is order-preserving. -/
theorem projCnt_mono {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    {p p' : SecCnt B A q} (hle : SecCntLe p p') :
    CPFLe (projCnt BC p) (projCnt BC p') := by
  intro ξ v hx
  cases hx with
  | intro a ha => exact ⟨a, hle (BC.b ξ) a ha.1, ha.2⟩

/-! ## Block density -/

/-- **Block-coding density.** For every countable condition `p`, every old
real `r`, there is a block index `α₀` and a stronger condition `p'` whose
projected bits on the whole block `blk α₀ n` equal `r n`. The fresh block
is provided by `block_fresh`, applied to the countable coverage of `p`'s
domain. -/
theorem denseBlock {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    (BCk : BlockCoding BC) (p : SecCnt B A q) (r : Nat → Bool) :
    ∃ (α₀ : I) (p' : SecCnt B A q), SecCntLe p p' ∧
      ∀ n, ∃ a, p'.rel (BC.b (BCk.blk α₀ n)) a ∧
        BC.bit (BCk.blk α₀ n) a = r n := by
  cases p.cnt with
  | intro c hcov =>
    cases BCk.block_fresh c.D c.hD c.w with
    | intro α₀ hα₀ =>
      have hfresh : ∀ n a, ¬ p.rel (BC.b (BCk.blk α₀ n)) a := by
        intro n a hrel
        cases hcov (BC.b (BCk.blk α₀ n)) a hrel with
        | intro d hd => exact hα₀ n d hd
      refine ⟨α₀, SecCnt.mk (fun bb a => p.rel bb a ∨
        ∃ n, bb = BC.b (BCk.blk α₀ n) ∧ (∀ a', ¬ p.rel bb a') ∧
          a = BC.codeBit (BCk.blk α₀ n) (r n))
        ?funi ?sec ?cnt, ?tail⟩
      case funi =>
        intro bb a a' h₁ h₂
        cases h₁ with
        | inl h₁ =>
          cases h₂ with
          | inl h₂ => exact p.funi bb a a' h₁ h₂
          | inr h₂ =>
            cases h₂ with
            | intro n hn => exact absurd h₁ (hn.2.1 a)
        | inr h₁ =>
          cases h₂ with
          | inl h₂ =>
            cases h₁ with
            | intro n hn => exact absurd h₂ (hn.2.1 a')
          | inr h₂ =>
            cases h₁ with
            | intro n hn =>
              cases h₂ with
              | intro n' hn' =>
                have hbb : BC.b (BCk.blk α₀ n) = BC.b (BCk.blk α₀ n') :=
                  hn.1 ▸ hn'.1
                have hblk : BCk.blk α₀ n = BCk.blk α₀ n' := BC.b_inj hbb
                have hnn : n = n' := (BCk.blk_inj α₀ α₀ n n' hblk).2
                cases hnn
                rw [hn.2.2, hn'.2.2]
      case sec =>
        intro bb a hba
        cases hba with
        | inl h => exact p.sec bb a h
        | inr h =>
          cases h with
          | intro n hn =>
            have ha : a = BC.codeBit (BCk.blk α₀ n) (r n) := hn.2.2
            have hbb : bb = BC.b (BCk.blk α₀ n) := hn.1
            rw [ha, hbb]
            exact BC.codeBit_fiber (BCk.blk α₀ n) (r n)
      case cnt =>
        refine ⟨Cover.mk (c.D ⊕ Nat) (countable_sum c.hD ⟨id, fun x y h => h⟩)
          (Sum.elim c.w (fun n => BC.b (BCk.blk α₀ n))), ?_⟩
        intro bb a hba
        cases hba with
        | inl h =>
          cases hcov bb a h with
          | intro d hd =>
            refine ⟨Sum.inl d, ?_⟩
            show c.w d = bb
            exact hd
        | inr h =>
          cases h with
          | intro n hn =>
            refine ⟨Sum.inr n, ?_⟩
            show BC.b (BCk.blk α₀ n) = bb
            rw [hn.1]
      case tail =>
        refine ⟨fun bb a hba => Or.inl hba, fun n => ?_⟩
        refine ⟨BC.codeBit (BCk.blk α₀ n) (r n),
          Or.inr ⟨n, rfl, hfresh n, rfl⟩,
          BC.codeBit_bit (BCk.blk α₀ n) (r n)⟩

/-! ## The block-decoder collapse -/

/-- **Collapse (relational).** A directed family `G` meeting every
block-coding requirement makes the generic binary function's block decoder
cover all old reals: for each `r` there is a block `α₀` such that for every
`n` the generic union at `b (blk α₀ n)` holds a value with bit `r n`.
Internally `α ↦ (bit (blk α n) (j(b (blk α n))))ₙ` is a surjection from the
ordinal-like index `I` onto `R_old`, so `R_old` becomes well-orderable. -/
theorem collapse_cnt {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    (BCk : BlockCoding BC)
    (G : SecCnt B A q → Prop)
    (hmeet : ∀ r : Nat → Bool, ∃ p, G p ∧ ∃ α₀,
      ∀ n, ∃ a, p.rel (BC.b (BCk.blk α₀ n)) a ∧ BC.bit (BCk.blk α₀ n) a = r n) :
    ∀ r : Nat → Bool, ∃ α₀, ∀ n, ∃ a, jrelCnt BC G (BC.b (BCk.blk α₀ n)) a ∧
      BC.bit (BCk.blk α₀ n) a = r n := by
  intro r
  cases hmeet r with
  | intro p hp =>
    cases hp.2 with
    | intro α₀ hα₀ =>
      refine ⟨α₀, fun n => ?_⟩
      cases hα₀ n with
      | intro a ha => exact ⟨a, ⟨p, hp.1, ha.1⟩, ha.2⟩

/-- The decoded generic bits are unique per position (functionality of the
internal block-decoder). -/
theorem collapse_cnt_fun {A B : Type} {q : A → B} {I : Type} (BC : BitCoding A B q I)
    (G : SecCnt B A q → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : SecCnt B A q, G p'' ∧
      SecCntLe p p'' ∧ SecCntLe p' p'')
    {ξ : I} {v v' : Bool}
    (h₁ : ∃ a, jrelCnt BC G (BC.b ξ) a ∧ BC.bit ξ a = v)
    (h₂ : ∃ a, jrelCnt BC G (BC.b ξ) a ∧ BC.bit ξ a = v') : v = v' := by
  cases h₁ with
  | intro a ha =>
    cases h₂ with
    | intro a' ha' =>
      cases ha.1 with
      | intro p hp =>
        cases ha'.1 with
        | intro p' hp' =>
          cases hdir p p' hp.1 hp'.1 with
          | intro p'' hp'' =>
            have hle1 : SecCntLe p p'' := hp''.2.1
            have hle2 : SecCntLe p' p'' := hp''.2.2
            have hval : a = a' :=
              p''.funi (BC.b ξ) a a' (hle1 (BC.b ξ) a hp.2) (hle2 (BC.b ξ) a' hp'.2)
            rw [← ha.2, ← ha'.2, hval]

end PPAC.Repair
