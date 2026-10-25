import DepthAspect.PrimePairBound

/-!
# The canonical finite trace-index sets in equations (33) and (43)

These definitions include every integer satisfying the strict elliptic
inequality and congruence. The finite intervals merely implement the sets;
the membership theorems remove the interval bounds completely.
-/
namespace DepthAspect.SurvivingTraces

/-- A finite interval containing every integer whose square is less than `m`. -/
noncomputable def squareInterval (m : ℤ) : Finset ℤ :=
  Finset.Icc (-(⌊Real.sqrt (m : ℝ)⌋₊ : ℤ)) (⌊Real.sqrt (m : ℝ)⌋₊ : ℤ)

theorem mem_squareInterval_of_square_lt {m x : ℤ} (hx : x ^ 2 < m) :
    x ∈ squareInterval m := by
  exact Finset.mem_Icc.mpr (PrimePairBound.radius_bound (B := (m : ℝ)) hx le_rfl)

/-- All surviving original trace indices `t`, with `Q=4q`. -/
noncomputable def survivingTraces (q m : ℤ) : Finset ℤ :=
  (squareInterval (4 * m)).filter (fun t => t ^ 2 < 4 * m ∧ 4 * q ∣ 4 * m - t ^ 2)

/-- All surviving halved trace indices `r`. -/
noncomputable def halvedTraces (q m : ℤ) : Finset ℤ :=
  (squareInterval m).filter (fun r => r ^ 2 < m ∧ q ∣ m - r ^ 2)

@[simp] theorem mem_survivingTraces (q m t : ℤ) :
    t ∈ survivingTraces q m ↔ t ^ 2 < 4 * m ∧ 4 * q ∣ 4 * m - t ^ 2 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨mem_squareInterval_of_square_lt h.1, h⟩

@[simp] theorem mem_halvedTraces (q m r : ℤ) :
    r ∈ halvedTraces q m ↔ r ^ 2 < m ∧ q ∣ m - r ^ 2 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨mem_squareInterval_of_square_lt h.1, h⟩

/-- Exact image identity underlying equation (43), including all indices. -/
theorem survivingTraces_eq_image (q m : ℤ) :
    survivingTraces q m = (halvedTraces q m).image (fun r => 2 * r) := by
  ext t
  constructor
  · intro ht
    obtain ⟨r, hr, hrl, hrd⟩ :=
      (LocalArithmetic.surviving_trace_iff q m t).mp ((mem_survivingTraces q m t).mp ht)
    exact Finset.mem_image.mpr ⟨r, (mem_halvedTraces q m r).mpr ⟨hrl, hrd⟩, hr.symm⟩
  · intro ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    exact (mem_survivingTraces q m (2 * r)).mpr
      ((LocalArithmetic.surviving_trace_iff q m (2 * r)).mpr
        ⟨r, rfl, (mem_halvedTraces q m r).mp hr⟩)

/-- The cardinality equality in (43). -/
theorem survivingTraces_card_eq (q m : ℤ) :
    (survivingTraces q m).card = (halvedTraces q m).card := by
  rw [survivingTraces_eq_image]
  apply Finset.card_image_of_injective
  intro a b hab
  change 2 * a = 2 * b at hab
  omega

/-- The exact trace-index set vanishes below `q`; primality is unnecessary. -/
theorem survivingTraces_empty_of_lt {q m : ℤ} (hmq : m < q) :
    survivingTraces q m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨r, _, hr, hd⟩ := (LocalArithmetic.surviving_trace_iff q m t).mp
    ((mem_survivingTraces q m t).mp ht)
  exact LocalArithmetic.no_surviving_trace_index hmq hr hd

end DepthAspect.SurvivingTraces
