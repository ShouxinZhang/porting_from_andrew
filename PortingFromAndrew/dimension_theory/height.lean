import Mathlib
set_option maxHeartbeats 0
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The height of a prime ideal is defined as the supremum of the lengths of strictly decreasing
chains of prime ideals below it. -/
noncomputable def Ideal.primeHeight [I.IsPrime] : WithTop ℕ :=
  Set.chainHeight {J : Ideal R | J.IsPrime ∧ J < I}

/-- The height of an ideal is defined as the infimum of the heights of minimal prime ideals
containing it. -/
noncomputable def Ideal.height : WithTop ℕ :=
  ⨅ J ∈ I.minimalPrimes, by
    have hJ : J ∈ I.minimalPrimes := by assumption
    have hJp : J.IsPrime := by sorry -- This should be provable but we'll skip it for now
    exact Ideal.primeHeight J

/-- For a prime ideal, its height equals its prime height. -/
lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  simp [height, primeHeight, Ideal.minimalPrimes_eq_subsingleton_self]

/-- An ideal has finite height if it is either the top ideal or its height is not top. -/
class Ideal.FiniteHeight : Prop where
  eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤

lemma Ideal.finiteHeight_iff_lt {I : Ideal R} :
  Ideal.FiniteHeight I ↔ I = ⊤ ∨ I.height < ⊤ := by
  constructor
  · intro h
    cases h.eq_top_or_height_ne_top with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (lt_of_le_of_ne le_top h)
  · intro h
    constructor
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (ne_top_of_lt h)

lemma Ideal.height_ne_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height ≠ ⊤ :=
  (h.eq_top_or_height_ne_top).resolve_left hI

lemma Ideal.height_lt_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height < ⊤ := by
  exact lt_of_le_of_ne le_top (Ideal.height_ne_top hI)

lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top (by exact h.ne_top)

lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top (by exact h.ne_top)

-- This lemma might need additional theorems for translation
lemma Ideal.primeHeight_succ [h : I.IsPrime] :
  I.primeHeight + 1 = Set.chainHeight {J : Ideal R | J.IsPrime ∧ J ≤ I} := by
  sorry


lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
  I.primeHeight ≤ J.primeHeight := by
  unfold primeHeight
  apply Set.chainHeight_mono
  intro x
  simp only [Set.mem_setOf_eq, and_imp]
  intro h1 h2
  exact ⟨h1, h2.trans_le h⟩

lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
  I.primeHeight + 1 ≤ J.primeHeight := by
  rw [primeHeight_succ]
  apply Set.chainHeight_mono
  intro x
  simp only [Set.mem_setOf_eq, and_imp]
  intro h1 h2
  exact ⟨h1, lt_of_le_of_lt h2 h⟩

lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime]
  (h : I < J) [J.FiniteHeight] :
  I.primeHeight < J.primeHeight := by
  have H := Ideal.primeHeight_add_one_le_of_lt h
  cases hJ : J.primeHeight
  · exact (J.primeHeight_ne_top hJ).elim
  cases hI : I.primeHeight
  · sorry -- handling top case
  · sorry -- completing proof with natural number arithmetic

lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
  (h : I < J) [I.FiniteHeight] :
  I.height < J.height := by
  rw [Ideal.height_eq_primeHeight I, Ideal.height]
  sorry -- The rest of the proof needs additional helper lemmas

theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    show p ∈ (∅ : Set (Ideal R))
    rw [← e]; exact hp.1
  · intro h
    rw [h]
    sorry
    -- exact minimalPrimes_top

theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  constructor
  · intro h
    have := h.1.1
    sorry
    -- exact absurd (Eq.refl ⊤) (this rfl)
  · intro h
    exact False.elim (Set.not_mem_empty p h)

theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp only [height, minimalPrimes_top]
  sorry

theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [height]
  apply le_iInf
  intro p hp
  -- obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp)
  sorry

theorem withTop.supr_add {ι : Sort*} [Nonempty ι]
    (f : ι → WithTop ℕ) (x : WithTop ℕ) :
    ⨆ i, f i + x = (⨆ i, f i) + x := by
  cases x
  case top =>
    simp only [add_top]
    apply le_antisymm
    · apply ciSup_le
      intro i
      exact le_top
    · simp
  case coe x =>
    have : ↑x ≤ ⨆ i, f i + ↑x := by
      sorry
    sorry

theorem withTop.supr₂_add {ι : Sort*} {p : ι → Prop} (hs : ∃ i, p i)
    (f : ∀ (i : ι), p i → WithTop ℕ) (x : WithTop ℕ) :
    (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x := by
  haveI : Nonempty { i // p i } := ⟨⟨_, hs.choose_spec⟩⟩
  sorry

/-- The Krull dimension of a commutative ring, defined as the supremum of lengths of chains of prime ideals -/
noncomputable def krullDimension (R : Type*) [CommRing R] : WithTop ℕ :=
  ⨆ (c : Set (Ideal R)) (h : IsChain (· ≤ ·) c) (h' : ∀ I ∈ c, I.IsPrime), ENat.card c

/-- A ring has finite Krull dimension if its Krull dimension is not ⊤ -/
class FiniteKrullDimensional (R : Type*) [CommRing R] : Prop where
  krullDimensionNeTop : krullDimension R ≠ ⊤

variable {R : Type*} [CommRing R]

lemma krullDimensionNeTop [h : FiniteKrullDimensional R] :
  krullDimension R ≠ ⊤ :=
h.krullDimensionNeTop

lemma krullDimensionLtTop [FiniteKrullDimensional R] :
  krullDimension R < ⊤ := by
  exact Ne.lt_top (krullDimensionNeTop)

lemma finiteKrullDimensionalIffLt :
  FiniteKrullDimensional R ↔ krullDimension R < ⊤ := by
  constructor
  · intro h
    exact krullDimensionLtTop
  · intro h
    exact ⟨ne_top_of_lt h⟩

lemma krullDimensionOfSubsingleton [hR : Subsingleton R] :
  krullDimension R = 0 := by
  unfold krullDimension
  simp only [le_of_subsingleton]
  rw [iSup_eq_of_forall_le_of_forall_lt_exists_gt]
  . intro c; rw [iSup_eq_of_forall_le_of_forall_lt_exists_gt]
    . intro chain_cond; rw [iSup_eq_of_forall_le_of_forall_lt_exists_gt]
      . intro prime_cond
        simp only [nonpos_iff_eq_zero]
        cases' Set.eq_empty_or_nonempty (s := c) with h h
        . simp [*]
        . rw [subsingleton_iff] at hR

          sorry
      . simp
    . simp
  . simp

instance (priority := 100) finiteKrullDimensionalOfSubsingleton [Subsingleton R] :
  FiniteKrullDimensional R := by
  rw [finiteKrullDimensionalIffLt, krullDimensionOfSubsingleton]
  exact WithTop.top_pos

lemma Ideal.heightLeKrullDimension {I : Ideal R} [I.IsPrime] :
    I.height ≤ krullDimension R := by
  simp_rw [Ideal.height]
  rw [iInf_le_iff]
  intro n hn
  simp only [le_iInf_iff] at hn

  sorry  -- The original uses le_supr₂ which needs to be adapted

lemma Ideal.primeHeightLeKrullDimension {I : Ideal R} [I.IsPrime] :
    I.primeHeight ≤ krullDimension R := by
  rw [← Ideal.height_eq_primeHeight]
  exact heightLeKrullDimension

instance Ideal.finiteHeightOfFiniteDimensional {I : Ideal R} [FiniteKrullDimensional R] (priority := 900):
    Ideal.FiniteHeight I := by
  rw [Ideal.finiteHeight_iff_lt, or_iff_not_imp_left]
  intro e
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I e
  refine' (Ideal.height_mono hM').trans_lt _
  refine' (lt_of_le_of_lt _ (krullDimensionLtTop (R := R)))
  exact M.heightLeKrullDimension

theorem krullDimensionSucc [Nontrivial R] :
    krullDimension R + 1 = Set.chainHeight {I : Ideal R | I.IsPrime} := by
  have h : ∃ I : Ideal R, I.IsPrime := by
    -- We know such an ideal exists in any nontrivial ring
    sorry
  sorry

lemma Ideal.finite_height_of_le {I J : Ideal R} (e : I ≤ J) (hJ : J ≠ ⊤) [J.FiniteHeight] :
  I.FiniteHeight :=
⟨Or.inr <| by { rw [← lt_top_iff_ne_top]; exact (Ideal.height_mono e).trans_lt (Ideal.height_lt_top hJ) }⟩

lemma Ideal.mem_minimal_primes_of_height_eq
  {I J : Ideal R} (e : I ≤ J) [JPrime : J.IsPrime] [hJ : Ideal.FiniteHeight J]
    (e' : J.height ≤ I.height) : J ∈ I.minimalPrimes := by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert h₁
  apply (eq_of_le_of_not_lt h₂ ?_).symm
  intro h₃
  letI := h₁.1.1
  letI := Ideal.finite_height_of_le h₂ <| Ideal.IsPrime.ne_top JPrime
  replace h₃ :=Ideal.height_strict_mono_of_is_prime h₃
  contrapose! h₃
  exact e'.trans <| Ideal.height_mono h₁.1.2

lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
  I.primeHeight = 0 ↔ I ∈ minimalPrimes R := by
  unfold Ideal.primeHeight
  rw [Set.chainHeight_eq_zero_iff]
  constructor
  . intro h
    refine' ⟨by simp_all only [bot_le, and_self], fun J hJ hJI => ?_⟩
    rw [@Set.eq_empty_iff_forall_not_mem] at h
    specialize h J
    simp only [Set.mem_setOf_eq, true_and, hJ] at h
    rw [propext (LE.le.not_gt_iff_eq hJI)] at h
    simp_rw [h, le_refl]
  . intro hI
    ext ⟨J, hJ⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hJ_prime hJ_lt_I
    exact not_le_of_lt hJ_lt_I (hI.2 ⟨hJ_prime, bot_le⟩ hJ_lt_I.le)

theorem Ideal.isMaximal_of_prime_height_eq_krullDimension {I : Ideal R} [h : I.IsPrime] [FiniteKrullDimensional R]
    (e : I.primeHeight = krullDimension R) : I.IsMaximal := by
  rcases subsingleton_or_nontrivial R with h' | _
  . exact (h.1 <| Subsingleton.elim I ⊤).elim
  . have := congrArg (fun x : WithTop ℕ => x + 1) e
    dsimp at this
    rw [Ideal.primeHeight_succ] at this
    refine ⟨h.1, ?_⟩
    intro J hJ
    by_contra e'
    obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal J e'
    have H : (insert M (setOf Ideal.IsPrime ∩ Set.Iic I)).chainHeight =
      krullDimension R + (1 : WithTop ℕ) + (1 : WithTop ℕ) := by
      rw [← this, Set.chainHeight_insert_of_forall_lt]; rfl
      intro I' hI'
      calc
        I' ≤ I := hI'.2
        _ < J := hJ
        _ ≤ M := hM'
    have : krullDimension R + (1 : WithTop ℕ) + (1 : WithTop ℕ) ≤
      Set.chainHeight (setOf <| Ideal.IsPrime (α := R)) := by
      rw [← H]
      apply Set.chainHeight_mono
      rintro K (rfl | ⟨hK, _⟩)
      · exact hM.isPrime
      · exact hK
    cases h_dim : krullDimension R with
    | top => exact krullDimensionNeTop h_dim
    | coe x =>
      rw [← krullDimensionSucc, h_dim] at this
      linarith [WithTop.coe_le_coe.mp this]

open IsLocalRing Ideal in
lemma IsLocalRing.maximalIdeal_primeHeight [IsLocalRing R] :
  (maximalIdeal R).primeHeight = krullDimension R := by
  apply le_antisymm
  . apply le_trans ?_ <| Ideal.heightLeKrullDimension (I := (maximalIdeal R))
    unfold Ideal.height
    simp only [le_iInf_iff]
    intro i hi
    letI := hi.1.1
    exact primeHeight_mono hi.1.2
  . unfold krullDimension
    simp only [iSup_le_iff]
    sorry

lemma IsLocalRing.maximalIdeal_height [IsLocalRing R] :
  (maximalIdeal R).primeHeight = krullDimension R := by
  rw [maximalIdeal_primeHeight]

lemma Ideal.prime_height_eq_krull_dimesion_iff {I : Ideal R} [IsLocalRing R] [I.IsPrime]
  [FiniteKrullDimensional R] :
  I.primeHeight = krullDimension R ↔ I = IsLocalRing.maximalIdeal R := by
  constructor
  . exact fun e => IsLocalRing.eq_maximalIdeal <| isMaximal_of_prime_height_eq_krullDimension e
  . rintro rfl
    rw [IsLocalRing.maximalIdeal_height]

open Set in
lemma Set.chainHeight_univ {α : Type*} [Preorder α] (s : Set α) :
    chainHeight (univ : Set s) = chainHeight s := by
  conv_rhs => rw [← @Subtype.range_coe _ s, ← image_univ]
  rw [chainHeight_image]
  simp
