import DepthAspect.OddTraceError
import DepthAspect.SignedHyperbolicBound

/-!
# Equation (112) for the actual spectral family

The arithmetic block estimates are applied at both parities to the
literal signed Hecke trace, after subtracting its literal hyperbolic
summand. The dimension inequality follows from the general Martin
formula, including depth seven. The error constant precedes all spectral
and class-number data.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set SignedSieve DyadicRamanujan DirichletRH GRHConsequences
open TraceWeightVariation
open scoped BigOperators SchwartzMap

noncomputable def primeHyperbolicTrace (k n P : ℕ) : ℂ :=
  (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (k + 1) * hyperbolicSieve (2 * k) n P /
    (((P : ℝ) ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)

theorem primeHyperbolicTrace_even (k a P : ℕ) (hP : P.Prime) :
    primeHyperbolicTrace k (2 * a + 4) P =
      (-1 : ℂ) ^ (k + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(k : ℝ)) : ℝ) : ℂ) := by
  unfold primeHyperbolicTrace hyperbolicSieve
  rw [hyperbolic_prime_even_sieve (2 * k) a P hP]
  have hp := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_div_hecke_power k P hP.pos)
  push_cast at hp
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  calc
    _ = -(-1 : ℂ) ^ (k + 1) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
      ((Real.sqrt P : ℂ) / (((P : ℝ) ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) := by
        push_cast
        ring
    _ = _ := by rw [hp]; ring

theorem primeHyperbolicTrace_odd (k a P : ℕ) (hP : P.Prime) :
    primeHyperbolicTrace k (2 * a + 5) P = 0 := by
  unfold primeHyperbolicTrace hyperbolicSieve
  rw [hyperbolic_prime_odd_sieve (2 * k) a P hP]
  simp

variable {k : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

noncomputable def ellipticPrimeTrace (S : SignedArithmeticData k Family Full New)
    (n P : ℕ) : ℂ :=
  S.primeSignedTrace (2 ^ n) P - primeHyperbolicTrace k n P

noncomputable def ellipticPrimeBlock (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (L s X Y : ℝ) (h : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ P ∈ (UnsignedDensity.primeBases L s).filter
      (fun P : ℕ => X < (P : ℝ) ∧ (P : ℝ) ≤ Y),
    ((Real.log (P : ℝ) / P : ℝ) : ℂ) * ellipticPrimeTrace S n P /
      (Fintype.card (Family (2 ^ n)) : ℂ) * h (Real.log (P : ℝ) / L)

/-- The same dimension bound used in the unsigned proof also holds at
n=7, by the exact odd-depth dimension formula. -/
theorem signed_dimension_lower (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (hn : 7 ≤ n) :
    (2 * (k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤
      (Fintype.card (Family (2 ^ n)) : ℝ) := by
  by_cases h8 : 8 ≤ n
  · have hb := MartinDimension.polynomial_degree_dimension_lower (2 * k) n h8
      (fun N => (Fintype.card (Family N) : ℝ)) S.unsigned.dimension_formula
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb
  · have hn7 : n = 7 := by omega
    subst n
    have he := MartinDimension.dimension_odd (2 * k + 2) 3 (by norm_num)
      (fun N => (Fintype.card (Family N) : ℝ)) S.unsigned.dimension_formula
    norm_num [oddDimension] at he ⊢
    rw [he]
    have := Nat.cast_nonneg (α := ℝ) k
    nlinarith

theorem signed_dimension_lower_weak (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (hn : 7 ≤ n) :
    (2 : ℝ) ^ n / 64 ≤ (Fintype.card (Family (2 ^ n)) : ℝ) := by
  have hb := signed_dimension_lower S n hn
  have hk := Nat.cast_nonneg (α := ℝ) k
  nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity]

theorem ellipticPrimeTrace_even (S : SignedArithmeticData k Family Full New)
    (a P : ℕ) (ha : 2 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    ellipticPrimeTrace S (2 * a + 4) P =
      latticeEllipticTrace k ((2 : ℝ) ^ (2 * a + 4))
        (evenLValue S.quadratic_class_formula a) P := by
  rw [ellipticPrimeTrace, primeSignedTrace_even_model S a P ha hP hodd,
    primeHyperbolicTrace_even k a P hP]
  ring

theorem ellipticPrimeTrace_odd (S : SignedArithmeticData k Family Full New)
    (a P : ℕ) (ha : 1 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    ellipticPrimeTrace S (2 * a + 5) P =
      latticeEllipticTrace k ((2 : ℝ) ^ (2 * a + 5))
        (oddLValue S.quadratic_class_formula a) P := by
  rw [ellipticPrimeTrace, primeSignedTrace_odd_model S a P ha hP hodd,
    primeHyperbolicTrace_odd k a P hP, sub_zero]

private theorem primeBases_prime_odd (L s : ℝ) (P : ℕ)
    (hP : P ∈ UnsignedDensity.primeBases L s) : P.Prime ∧ Odd P := by
  have hp := (Finset.mem_filter.mp hP).2
  exact ⟨hp.1, hp.1.odd_of_ne_two hp.2⟩

theorem ellipticPrimeBlock_even (S : SignedArithmeticData k Family Full New)
    (a : ℕ) (ha : 2 ≤ a) (L s X Y : ℝ) (h : 𝓢(ℝ, ℂ)) :
    ellipticPrimeBlock S (2 * a + 4) L s X Y h =
      primeTraceBlock k ((2 : ℝ) ^ (2 * a + 4))
        (Fintype.card (Family (2 ^ (2 * a + 4))) : ℝ) L X Y h
        (UnsignedDensity.primeBases L s) (evenLValue S.quadratic_class_formula a) := by
  have hd := signed_dimension_lower_weak S (2 * a + 4) (by omega)
  rw [primeTraceBlock_eq_latticeTraceSum k
    (N := (2 : ℝ) ^ (2 * a + 4))
    (d := (Fintype.card (Family (2 ^ (2 * a + 4))) : ℝ)) (by positivity)
    (lt_of_lt_of_le (by positivity) hd) L X Y h (UnsignedDensity.primeBases L s)
    (fun P hP => (primeBases_prime_odd L s P hP).1.pos)
    (evenLValue S.quadratic_class_formula a)]
  unfold ellipticPrimeBlock
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hprime, hodd⟩ := primeBases_prime_odd L s P (Finset.mem_filter.mp hP).1
  rw [ellipticPrimeTrace_even S a P ha hprime hodd]
  norm_cast

theorem ellipticPrimeBlock_odd (S : SignedArithmeticData k Family Full New)
    (a : ℕ) (ha : 1 ≤ a) (L s X Y : ℝ) (h : 𝓢(ℝ, ℂ)) :
    ellipticPrimeBlock S (2 * a + 5) L s X Y h =
      primeTraceBlock k ((2 : ℝ) ^ (2 * a + 5))
        (Fintype.card (Family (2 ^ (2 * a + 5))) : ℝ) L X Y h
        (UnsignedDensity.primeBases L s) (oddLValue S.quadratic_class_formula a) := by
  have hd := signed_dimension_lower_weak S (2 * a + 5) (by omega)
  rw [primeTraceBlock_eq_latticeTraceSum k
    (N := (2 : ℝ) ^ (2 * a + 5))
    (d := (Fintype.card (Family (2 ^ (2 * a + 5))) : ℝ)) (by positivity)
    (lt_of_lt_of_le (by positivity) hd) L X Y h (UnsignedDensity.primeBases L s)
    (fun P hP => (primeBases_prime_odd L s P hP).1.pos)
    (oddLValue S.quadratic_class_formula a)]
  unfold ellipticPrimeBlock
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hprime, hodd⟩ := primeBases_prime_odd L s P (Finset.mem_filter.mp hP).1
  rw [ellipticPrimeTrace_odd S a P ha hprime hodd]
  norm_cast

/-- Literal equation (112), uniformly over the spectral data and over
both parities of depth. All internal trace, prime-average, dimension,
index-count, variation, and main-term identities are discharged. -/
theorem signed_prime_elliptic_block_bound (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SignedArithmeticData k Family Full New)
      (n : ℕ), 7 ≤ n → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ‖ellipticPrimeBlock S n L s X Y h -
        (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ n)
          (Fintype.card (Family (2 ^ n)) : ℝ) *
          MurmurationArithmetic.M k 2 (u / ((2 : ℝ) ^ n)) / u) •
            h (Real.log u / L))‖ ≤
        C * ((((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (1 / 4 + ε) +
          (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (3 / 4 + ε)) := by
  obtain ⟨Ce, hCe, hbe⟩ := even_trace_block_bound hRH cited hε
  obtain ⟨Co, hCo, hbo⟩ := odd_trace_block_bound hRH cited hε
  let A := (2 + (2 * (k : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h
  have hA : 0 ≤ A := by dsimp [A, schwartzSize]; positivity
  refine ⟨(Ce + Co) * (A + 1), by positivity, ?_⟩
  intro S n hn X Y L s hX hXY hY hY3 hL hYs
  have hdim := signed_dimension_lower_weak S n hn
  have hE : 0 ≤ (((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (1 / 4 + ε) +
      (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (3 / 4 + ε) := by positivity
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨b, hb⟩ := heven
    let a := b - 2
    have heq : n = 2 * a + 4 := by dsimp [a]; omega
    have ha : 2 ≤ a := by omega
    rw [heq] at hdim hE ⊢
    rw [ellipticPrimeBlock_even S a ha]
    have hbound := hbe S.quadratic_class_formula k a ha X Y L s _
      hX hXY hY hY3 hL hYs hdim h
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hE)
    change Ce * A ≤ (Ce + Co) * (A + 1)
    nlinarith
  · obtain ⟨b, hb⟩ := hodd
    let a := b - 2
    have heq : n = 2 * a + 5 := by dsimp [a]; omega
    have ha : 1 ≤ a := by omega
    rw [heq] at hdim hE ⊢
    rw [ellipticPrimeBlock_odd S a ha]
    have hbound := hbo S.quadratic_class_formula k a ha X Y L s _
      hX hXY hY hY3 hL hYs hdim h
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hE)
    change Co * A ≤ (Ce + Co) * (A + 1)
    nlinarith

end DepthAspect.SignedDensity
