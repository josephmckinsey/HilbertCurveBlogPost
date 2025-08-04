import VersoBlog
import HilbertCurveBlogPost.CommonElements
import HilbertCurve

open Verso Genre Blog
open Verso.Doc

set_option pp.rawOnError true

-- I removed some definitions, and now this is necessary...
set_option maxHeartbeats 800000

#doc (Page) "Formalizing Hilbert Curves in Lean" =>

The famous Hilbert curve has a simple inductive construction, but key portions use analysis. [Lean](https://lean-lang.org) should be an ideal proof assistant for applying the key mathematical principles. In my [last post](https://josephmckinsey.com/hilbertcurves.html), I walked through informal definitions and proofs. The following concerns a more sophisticated perspective on how Lean can undertake this sort of mathematics.

::::blob hilbert_curve_123
::::

I'll present some of my formalization below using Verso, Lean's new HTML generation tool, but I'll also tell you about the other interesting facts you learn by thinking hard about every detail while coding a formalization, such as Höllder continuity, computability, partial invertibility, etc. Despite disappointing AI provers, promising inline visualizations with ProofWidgets, and our lovely library of math [`mathlib`](https://github.com/leanprover-community/mathlib4), the challenging gaps left by spatial intuition leave a lot of gnarly induction, casework, and algebra, along with some confusing remnants from `mathlib` and Lean's casting rules.

1. {label notation_section}[Notation for the Hilbert Curve]
2. {ref leandesign}[Lean Design Decisions and Selected Proofs]
3. {ref additionaldirections}[Additional Directions]
4. {ref proscons}[Pros and Cons of using Lean here]
5. {ref conclusion}[Conclusion]
6. {ref verso}[P.S. Verso is fine]

# {label notation_section}[Mathematical Notation for the Hilbert Curve]

We will construct integer versions of the Hilbert curve denoted as $`H_n(i)` where $`n` and $`i` are natural numbers, and $`H_n(i)` is a pair of natural numbers.

When we interpolate and scale down the integer versions, we'll use $`\tilde{H}_i(t)`.

Finally when we pass to the limit and get the final curve, as $`H(t)` with no superscript or subscript.

# {label leandesign}[Lean Design Decisions and Selected Proofs]

If you don't care about the details of Lean proofs, then I would skip this section, so go to {ref additionaldirections}[Additional Directions]. If you are mildly interested, please skim all the proofs!

In our proofs in the [previous post](https://josephmckinsey.com/hilbertcurves.html), I did mention the explicit definitions of eahc version, however most of the proofs deferred the case-work and algebra to the reader. Often, the truth of the statement is completely obvious from the pictures involved, such as the bounds and injectivity of the integer case $`H_i(n)`. Of course, this is insufficient for a truly formal proof as in Lean 4. The primary tool for the low-level definitions is essentially always induction, but we still need to label the different cases.

Filling out the details here will involve explaining to Lean what a "quadrant" is, how the various intervals map to those quadrants, and explaining in detail what each transformation does, and defining their properties. In particular, the later proofs require continuity assumptions.

Additionally, there are some activities that seem to be mildly inadequately covered in Lean's `mathlib`: casting from $`\mathbb{N} \times \mathbb{N}` to $`\mathbb{Z} \times \mathbb{Z}` and to $`\mathbb{R} \times \mathbb{R}`, linear interpolation, and a few proofs about floors.

## {label leantransformations}[Transformations and Quadrants]

I define a custom name for the lengths, since it appeared as a very common repeated expression. In retrospect, I probably would I have used $`4^n` and made the term reducible to `4^n` automatically, but you live and learn. I would not be surprised if
my other choices here were somewhat suboptimal, especially the quadrants.

```leanInit notOpen
```

```leanInit openNames
open HilbertCurve
```

```lean notOpen
def hilbert_length (i : ℕ) := 2^(2*i)
```

For each of the integer transformations, we'll need some code.

```lean notOpen
def T0_nat : ℕ × ℕ → ℕ × ℕ := Prod.swap
def T1_nat (i : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ := mn + (0, 2^i)
def T2_nat (i : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ := mn + (2^i, 2^i)
def T3_nat (i : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ := (2^(i+1) - 1, 2^i - 1) - mn.swap
```

Since the natural numbers are truly awful once you have subtraction, we have a ring version that applies any ring, so we get $`\mathbb{Z}` and $`\mathbb{R}`. Since we have this more general statements, we drop the `_nat`.

```lean notOpen
variable {R : Type*} [Ring R]

def T3 (i : ℕ) : R × R →ᵃ[R] R × R := {
  toFun := fun mn => (2^(i+1) - 1, 2^i - 1) - mn.swap
  linear := -HilbertCurve.T0
  map_vadd' p v := by
    simp [HilbertCurve.T0]
    set a := ((2 : R)^(i + 1) - 1, (2 : R)^i - 1)
    -- For some reason, ring doesn't work
    rw [add_comm, add_comm (-v.swap)]
    rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add]
}
```

For each of these, we'll need quite a few lemmas for casting them which depend on bounds.

```lean notOpen
lemma T3_cast_nat (i : ℕ) (mn : ℕ × ℕ) (h1 : mn.1 ≤ 2^i - 1) (h2 : mn.2 ≤ 2^(i+1) - 1) :
  T3 i (mn : R × R) = T3_nat i mn := by
  simp only [T3_nat, T3, Prod.swap, Prod.mk_sub_mk, RtimesR.coe_prod]
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  simp
```

We will need to deal with a lot of different lemmas and casework about quadrants, so we'll create code for the transformations themselves.

```lean notOpen
inductive Quadrant where
| BOTTOM_LEFT | TOP_LEFT | TOP_RIGHT | BOTTOM_RIGHT
deriving DecidableEq
```

We'll need functions to then understand how we divide our input $`\mathbb{N}` into quadrants as well as $`\mathbb{N} \times \mathbb{N}` (which will be `get_quadrant'`). You might note that $`i` here will be the divisions of $`H_{i+1}`, and this is designed to work better with the pattern matching.

```lean notOpen
def get_quadrant (i n : ℕ) : Quadrant :=
  if n < hilbert_length i then
    Quadrant.BOTTOM_LEFT
  else if n < 2 * hilbert_length i then
    Quadrant.TOP_LEFT
  else if n < 3 * hilbert_length i then
    Quadrant.TOP_RIGHT
  else
    Quadrant.BOTTOM_RIGHT
```

Each of these quadrants will also have a few "equal" lemmas like `bottom_left_eq : get_quadrant i n = Quadrant.BOTTOM_LEFT ↔ n < hilbert_length i`. These statements seem required in my definition, which actually makes me think my definition is pretty bad.

## {label leaninteger}[The Integer Version]

Finally, we can explain the definition of our first Hilbert curve:

```lean notOpen
def hilbert_curve : ℕ → ℕ → (ℕ × ℕ)
| 0 => fun _ => (0, 0)
| .succ i => fun n => match get_quadrant i n with
  | Quadrant.BOTTOM_LEFT =>
    let h := hilbert_curve i n
    T0_nat h
  | Quadrant.TOP_LEFT => let h := hilbert_curve i (n - hilbert_length i)
    T1_nat i h
  | Quadrant.TOP_RIGHT => let h := hilbert_curve i (n - 2*hilbert_length i)
    T2_nat i h
  | Quadrant.BOTTOM_RIGHT =>
    let h := hilbert_curve i (n - 3*hilbert_length i)
    T3_nat i h
```

Although this version has all the abbreviations such as `Quadrant.BOTTOM_LEFT` and `get_quadrant`. Those can be included inline without much loss in clarity, but the Lean proofs become much more difficult once casework gets involved.

Unlike the normal presentation of the Hilbert curve, we have a definition for the $`n = 0` case, $`H_0(i) = (0, 0)`. For $`i \ge 1`, we can then divide everything up into quadrants, then apply each transformation, and recurse.

Before it is time to prove theorems, it is important to test definitions like this. My first few definitions had some sign and off-by-one errors which can be found with testing:

```lean notOpen
/--
info: [(0, 0), (0, 1), (1, 1), (1, 0)]
-/
#guard_msgs in
#eval List.map (hilbert_curve 1) (List.range (2^2))
```

Using [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) , we can also display these, which makes the nature of a bug extremely obvious. By giving the examples folder of ProofWidgets to any modern LLM (I used Gemini), you can generate SVG which displays in the Lean InfoView [`#html (hilbert_curve_svg 3).toHtml`](https://github.com/josephmckinsey/LeanHilbertCurves/blob/325dc26792e216989d0a713696a698db04e9d7b6/HilbertCurve/Pictures.lean#L57) right next to your goals and hypotheses:

::::blob hilbert_curve_3
::::

These pictures can be quite helpful, since they can let you verify hypotheses experimentally before committing to a precise, yet wrong statement. Ever since [@thingskatedid](https://twitter.com/thingskatedid/status/1386077306381242371) inspired me, I've been enjoying the fruits of visualizations created with throwaway Javascript.

Since I know how annoying extra conditions can get, all of my functions use "normal" types like `ℕ` instead of `Fin n`. I didn't test this design decision, so maybe adding dependent information isn't _so_ bad. Beyond the typical input bounds, our definition naturally makes the curve constant.

### {label leanintproofs}[Some formal proofs about integers]

To actually prove injectivity and surjectivity, I decided to implement the inverse, which made preliminary testing easy. Formally verifying it amounted to a lot of casework and induction. For the casework, we have to prove that each of the transformations actually preserve the quadrants. Each one is basic algebra (modulo annoying casting).

```lean openNames
open HilbertCurve
#check get_quadrant'_T0
example (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T0_nat mn) = Quadrant.BOTTOM_LEFT := by
  simp only [get_quadrant', T0_nat]
  have : 2^i - 1 < 2^i := by simp
  rw [if_pos, if_pos]
  · apply lt_of_le_of_lt h.1 this
  apply lt_of_le_of_lt h.2 this
```

which then let us decompose the `hilbert_curve`

```lean openNames
#check quadrant_preserved
example (i n : ℕ) : get_quadrant' i (hilbert_curve (i+1) n) = get_quadrant i n := by sorry
```

and finally we can finish with a bunch of induction. As a reminder, you can hover or click elements to get details!

```lean openNames
#check hilbert_curve_injective
/--
A hilbert curve is injective on its length
-/
example (i : ℕ) (n : ℕ) (h : n < hilbert_length i) :
  hilbert_inverse i (hilbert_curve i n) = n := by
  induction i generalizing n with
  | zero =>
    simp [hilbert_length] at h
    rw [h]
    simp [hilbert_curve, hilbert_inverse]
  | succ i ih =>
    have := quadrant_preserved i n
    set q := get_quadrant i n with q_def
    unfold hilbert_inverse
    rw [this]
    rcases q <;> dsimp <;> unfold hilbert_curve <;> rw [<-q_def]
    · simp  [T0_involutive]
      apply ih
      exact (bottom_left_eq i n).mp (Eq.symm q_def)
    · simp only
      rw [T1_inv_of_T1_nat]
      have := (top_left_eq i n).mp (Eq.symm q_def)
      rw [ih (n - hilbert_length i)]
      · omega
      omega
    · simp only
      rw [T2_inv_of_T2_nat]
      have := (top_right_eq i n).mp (Eq.symm q_def)
      rw [ih (n - 2*hilbert_length i)]
      · omega
      omega
    simp only
    have size := hilbert_curve_size i (n - 3 * hilbert_length i)
    rw [T3_inv_of_T3_nat]
    · rw [ih _]
      · have := (bottom_right_eq i n).mp (Eq.symm q_def)
        omega
      rw [hilbert_length_succ] at h
      omega
    · exact size.1
    apply le_trans size.2
    omega
```

As you can see, it seems that a lot of the "obvious" proofs I skipped in the informal post run into hundreds of lines of code once you spell it all out. After thinking about it, I think that turning a picture into mathematics involves encoding a lot of geometry we humans have very well internalized, sort of like how it took many decades to program the difference between a cat and a bird reliably.

The surjectivity proofs ended up committing a similar level of "collateral damage". To prove the Hilbert curve only moves by 1 each step, a similar level of boilerplate shows that the quadrants "connect" with each transformation. I had to define a little l1 norm `dist'` for pairs of integers, which feels like it _should_ exist somewhere. If you know of where to look, please reach out.

I am at a bit of a loss of how to make this simple. It all feels extremely basic, but there was so many definitions involved here.

### {label leancauchy}[Cauchy Condition]

::::blob hilbert_curve_comparison23
::::

After staring at several diagrams comparing the different curves, I came up with the following statement:

```lean notOpen
/-
Each iteration subdivides each square
-/
lemma subdivision_size (i n : ℕ) :
  2 * hilbert_curve i (n/4) ≤ hilbert_curve (i+1) n ∧
  hilbert_curve (i+1) n ≤ 2 * hilbert_curve i (n/4) + 1 := by sorry
```

I won't bore you with the proof, except that in addition to induction, we also need some extra definitions and proofs for each transformation:

```lean notOpen
def within_square (a b : ℕ × ℕ) : Prop :=
  2•a ≤ b ∧ b ≤ 2•a+1

lemma T1_within_square (i : ℕ) (mn1 mn2 : ℕ × ℕ) :
  within_square mn1 mn2 →
  within_square (T1_nat i mn1) (T1_nat (i+1) mn2) := by
  simp [within_square, T1_nat]
  intro h1 h2
  have : 2 * mn1.1 ≤ mn2.1 := h1.1
  have : 2 * mn1.2 ≤ mn2.2 := h1.2
  have : mn2.1 ≤ 2*mn1.1 + 1 := h2.1
  have : mn2.2 ≤ 2*mn1.2 + 1 := h2.2
  constructor <;> constructor
  <;> (simp [pow_add]; omega)
```

## {label leancasting}[A digression on casting and pairs]

The biggest obstacle to algebra in Lean is that you need to do a lot of casting. Often times, statements on $`\mathbb{N}` which are trivial for integers or reals requires a lot of intermediate bound proofs to satisfy the conditions for `Nat.cast_sub`.  I decided that if the tactic `omega` ever failed, I would try converting to integers, but luckily `omega` covers a lot.

Unfortunately, pairs and casting pairs are not very well covered by `mathlib`, so I have a few definitions and lemmas like:

```lean notOpen
#check NtimesN.toRtimesR

@[coe]
example : ℕ × ℕ → R × R := fun p => (p.1, p.2)

instance : Coe (ℕ × ℕ) (R × R) where
  coe := NtimesN.toRtimesR
```

The less obvious and more annoying part comes from missing instances for ordered rings on products:
```lean notOpen
instance {α : Type} [PartialOrder α] [Ring α] [IsStrictOrderedRing α] :
  IsOrderedRing (α × α) := by sorry
```

I discovered these instances didn't appear to exist when I actually read through the ordered ring lemmas instead of just searching for lemmas. I wouldn't be surprised if these already exist _somewhere_ or if there was a good reason not too.

## {label leaninterpolation}[Interpolating]

To construct our interpolated version of the Hilbert curve, first we must define an API for interpolation. In `mathlib`, we have the ability to (1) concatenate paths and (2) use `AffineMap.lineMap` to connect points. Unfortunately, blindly concatenating paths is not so nice, since it always compresses the two arguments to $`[0, \frac{1}{2}]` and $`[\frac{1}{2}, 1]`. Repeated application does not evenly space points, which we need. So instead, we'll need to define linear interpolation:

```lean notOpen
#check interpolate_points
noncomputable example (f : ℤ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  let n := ⌊t⌋
  (AffineMap.lineMap (f n) (f (n+1))) (t - ⌊t⌋)
```

Here, `AffineMap.lineMap` is exactly the $`(1 - t)x  + t y = x + t (y - x)` but for affine spaces. I didn't bother to generalize this definition, but affine spaces seem like a convenient target. I also find this definition to be much simpler than the "informal" definition, which is a nice change. You may notice that it is noncomputable. This is because the floor function is terribly annoying, but the computable alternative here is also a chore. I'll leave it as an exercise for the reader to construct a computable version.

There are a few theorems for interpolation that are all fairly obvious. Remember you can hover or click to to get description and docs
- `interpolate_interpolates`
- `interpolate_add`  and `interpolate_add'`
- `interpolate_eq_affine_map`
- `interpolate_section`
- `interpolate_preserves`: this one was actually difficult to prove, since it involved some strange use of `Set.Accumulate`.
- `interpolate_map` and `interpolate_map'`
- `interpolate_is_continuous`
- `interpolate_distance`

Proving `interpolate_is_continuous` required using `LocallyFinite.continuous`. Trying to compose lots of continuous functions can be abused by interleaving them, and I refuse to "manually" use continuity here. Our "component" intervals $`[i, i+1]` cover each point at most twice. I found this to be completely obvious, but also very annoying to prove, so I prove at most 3 or 4 times with the use of the $`\lfloor \cdot \rfloor` and $`\lfloor \cdot \rfloor`.

I suspect that these proofs can be reordered and streamlined as well as obviously extended to some really nice space. I am wary of standardizing too soon, since minor extensions like adding circular arcs are still a huge pain. There are plenty of questions like "why make them evenly spaced".

## {label leannormalized}[Scaling and Normalized Version]

I often wanted to break things up into a "core" interpolated version and then compose it with linear functions for scaling. Oddly enough, the "scale" linear function didn't appear anywhere. I'm not sure if it's even necessary, but I implemented it:

```lean notOpen
/--
scale is smul as a LinearMap
-/
@[reducible]
noncomputable def scale (s : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => s • x
    map_add' := by simp
    map_smul' := by simp; ring_nf; simp
  }
```

Now, defining the final interpolated version involves stitching this together (+ casting :( )

```lean notOpen
/--
An iteration of the Hilbert curve as ℝ → ℝ × ℝ interpolated
and scaled to [0, 1] × [0, 1].
-/
noncomputable def normalized_hilbert_curve (i : ℕ) :=
  interpolate_points (
    scale ((2 : ℝ)^i)⁻¹ ∘ (↑) ∘ hilbert_curve i ∘ (fun x ↦ x.toNat)
  ) ∘ (fun t ↦ t * hilbert_length i)
```

Continuity ends up being extremely simple:

```lean openNames
#check normal_hilbert_curve_continuous
/--
Each real Hilbert curve is continuous.
-/
example (i : ℕ) : Continuous (normalized_hilbert_curve i) := by
  rw [normalized_hilbert_curve]
  set f : ℤ → ℝ × ℝ := (⇑(scale (2 ^ i)⁻¹) ∘ (fun x ↦ (↑x.1, ↑x.2)) ∘ hilbert_curve i ∘ fun x ↦ x.toNat) with f_def
  have := interpolate_is_continuous f
  apply Continuous.comp this
  apply continuous_mul_right
```

Once I had the distance lemma `normal_subdivision_size` informally, writing it in Lean didn't need _too_ much creatively, except for this missing floor lemma which I had to prove "by definition".

```lean notOpen
/--
If you multiply by n, floor, then integer divide by n, then it is the same as floor.
-/
lemma div_floor_mul_eq_floor (t : ℝ) (n : ℕ) (h : 0 ≤ t) (h' : 0 < n):
  ⌊t * n⌋ / n = ⌊t⌋ := by sorry
```

```lean openNames
#check normal_subdivision_size
/--
The real Hilbert curve only moves 1 / 2^(i-1) each iteration for each t.
-/
example (i : ℕ) (t : ℝ) :
  dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve (i+1) t) ≤ 2 * (2^i)⁻¹ := by
  -- We'll prove this by the triangle inequality between H_i(t), H_i(n / L_i),
  -- H_{i+1}(n / L_{i+1)}), and finally H_{i+1}(t). We do this instead
  -- of a more obvious subdivision lemma since the edge effects at the boundary
  -- are too annoying.
  apply le_trans (dist_triangle4 _
    (normalized_hilbert_curve i (⌊t * hilbert_length i⌋ / hilbert_length i))
    (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i + 1))))
    _)
  -- Bounding the distance between points t and n / L_i is still easy.
  have t1 : dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve i (↑⌊t * ↑(hilbert_length i)⌋ / ↑(hilbert_length i))) ≤ (2^i)⁻¹ :=
    normal_hilbert_dist i t
  have t3 : dist (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i+1))))
    (normalized_hilbert_curve (i+1) t) ≤ (2^(i+1))⁻¹ := by
    rw [dist_comm]
    exact normal_hilbert_dist (i+1) t
  have t2 : dist (normalized_hilbert_curve i (⌊t * (hilbert_length i)⌋ / (hilbert_length i)))
    (normalized_hilbert_curve (i+1) (⌊t * hilbert_length (i+1)⌋ / (hilbert_length (i+1)))) ≤ (2^(i+1))⁻¹ := by
    -- When t ≤ 0, it's a straightforward calculation.
    by_cases h : t ≤ 0
    · have : ∀n : ℕ, ⌊t * n⌋ / n ≤ (0 : ℝ) :=  by
        intro n
        apply div_nonpos_of_nonpos_of_nonneg
        · norm_cast
          apply Int.floor_nonpos
          apply mul_nonpos_of_nonpos_of_nonneg
          exact h
          simp only [Nat.cast_nonneg]
        simp only [Nat.cast_nonneg]
      rw [normalized_hilbert_curve_nonpos i _ (this (hilbert_length i))]
      rw [normalized_hilbert_curve_nonpos (i+1) _ (this (hilbert_length (i+1)))]
      rw [normal_hilbert_start, normal_hilbert_start]
      simp
    simp only [not_le] at h
    -- Now we can relate the ⌊n⌋ = ⌊4 * n⌋ / 4
    have : ⌊t * hilbert_length i⌋ = ⌊t * hilbert_length (i+1)⌋ / 4 := by
      rw [hilbert_length_succ, mul_comm 4]
      rw [Nat.cast_mul, Nat.cast_ofNat]
      rw [<-mul_assoc]
      symm
      apply div_floor_mul_eq_floor
      · positivity
      norm_num
    rw [this]
    -- We need to deal with some toNat casting to apply normal_hilbert_across_dist
    rw [show ⌊t * hilbert_length (i+1)⌋ = ⌊t * hilbert_length (i+1)⌋.toNat by
      refine Int.eq_natCast_toNat.mpr ?_
      positivity
    ]
    rw [show ⌊t * hilbert_length (i+1)⌋.toNat / (4 : ℤ) = (⌊t * hilbert_length (i+1)⌋.toNat / 4 : ℕ) by
      simp
    ]
    have : ∀n : ℕ, ((n : ℤ) : ℝ) = (n : ℝ) := by intro n; norm_cast
    rw [this, this]
    apply normal_hilbert_across_dist
  rw [show 2  * ((2 : ℝ)^i)⁻¹ = (2^i)⁻¹ + (2^(i+1))⁻¹ + (2^(i+1))⁻¹ by
    rw [pow_add]
    ring
  ]
  linarith
```

From this, we easily get a Cauchy sequence `normal_is_cauchy`.

To prove "approximate" surjectivity, we can use the floor function _except_ for the top and right edge, which we have to do manually. Because we already lost computability, we can use classical logic and simplify our life a bit. We'll go even further and turn this existential into a left-inverse too.

- {lean openNames}`exists_normal_hilbert_approx_inv`
- {lean openNames}`norm_hilbert_inv`

## {label leanlimit}[Limit Definition]

Our final limit definition is straightforward at this point:

```lean openNames
#check limit_hilbert_curve_exists
/--
The real Hilbert converges at each point.
-/
example (t : ℝ) :
  ∃x, Filter.Tendsto (normalized_hilbert_curve · t) Filter.atTop (nhds x) := by
  apply cauchySeq_tendsto_of_complete
  exact normal_is_cauchy t

/-- Name has a ' to avoid name conflicts. -/
noncomputable def limit_hilbert_curve' (t : ℝ) : ℝ × ℝ :=
  Classical.choose (limit_hilbert_curve_exists t)
```

Many of the remaining difficulties concern the difficulties of computing limits, which appears to have some fundamental complexity. On the technical side, `mathlib`'s definition of uniform convergence is extremely general. It uses ["Uniformity Spaces"](https://en.wikipedia.org/wiki/Uniform_space) (mathlib: [Mathlib.Topology.UniformSpaces.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Defs.html)). I am luckily familiar enough with topological groups that nothing scared me _too_ much, since otherwise this might have required more effort to get used to.

Each of our proofs, such as surjectivity, go through the same sort of steps at this point: (1) choose a really nice sequence that we can evaluate at the interpolated version, (2) choose an even nicer subsequence that converges, and then (3) use unique and uniform convergence to lift it back up to `limit_hilbert_curve`.

```lean openNames
#check limit_hilbert_surj_on
/-
The limit touches every point in [0,1]×[0,1]
-/
example :
  Set.SurjOn limit_hilbert_curve (Set.Icc 0 1) (Set.Icc 0 1) := by
  intro x xy
  -- Since [0, 1] is compact, we can lift the approximate norm_hilbert_inv to
  -- a convergent subsequence.
  have : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨t, th, φ, φh, h⟩ := this.tendsto_subseq (norm_hilbert_inv_bounded (xh := xy) (x := x))
  use t, th
  set f := fun n ↦ norm_hilbert_inv n x xy
  -- Now we use the uniform convergence to show that we the hilbert curve converges
  -- on the subsequence of f to limit_hilbert_curve t
  have h' : Filter.Tendsto (fun i ↦ normalized_hilbert_curve (φ i) (f (φ i)))
    Filter.atTop (nhds (limit_hilbert_curve t)) :=
    TendstoUniformly.tendsto_comp
      ((tendstoUniformly_iff_seq_tendstoUniformly.mp limit_hilbert_curve_tendstouniformly) φ
        (StrictMono.tendsto_atTop φh))
      (Continuous.continuousAt limit_hilbert_continuous)
      h
  apply tendsto_nhds_unique h'
  -- Now all that remains is to show that it also converges to x
  apply (Filter.tendsto_iff_seq_tendsto (k := Filter.atTop) (
    f := fun i ↦ normalized_hilbert_curve i (f i)
  )).mp ?_ φ (StrictMono.tendsto_atTop φh)
  -- We can use the bound from the approximate inverse to guarantee convergence.
  rw [tendsto_iff_dist_tendsto_zero]
  have : Filter.Tendsto (fun n => ((2 : ℝ) ^ n)⁻¹) Filter.atTop (nhds 0) := by
    rw [show (fun n ↦ ((2 : ℝ)^n)⁻¹) = fun n ↦ ((2 : ℝ)⁻¹)^n by
      simp]
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs]
    norm_num
  apply squeeze_zero (fun n ↦ dist_nonneg) (g0 := this)
  intro n
  rw [dist_comm]
  exact norm_hilbert_inv_dist n x xy
```

For the symmetries, we use uniform continuity of transformations to preserve uniform convergence. To get uniform continuity of each transformation, there's some new definitions, plus some little lemmas I defined to get `AffineMap.toContinuousAffineMap` for finite-dimensional spaces and `ContinuousAffineMap.uniformContinuous`.

```lean notOpen
noncomputable def T3_real (i : ℕ) : ℝ × ℝ →ᴬ[ℝ] ℝ × ℝ :=
  let id := (LinearMap.id (M := ℝ × ℝ) (R := ℝ))
  let post := (1 / (2^(i+1)) : ℝ) • id
  let pre := (2^i : ℝ) • id
  AffineMap.toContinuousAffineMap <|
    (post.toAffineMap.comp (T3 i)).comp
    pre.toAffineMap

noncomputable def T3_real_lim : ℝ × ℝ →ᴬ[ℝ] ℝ × ℝ :=
  AffineMap.toContinuousAffineMap {
    toFun := fun x ↦ (1, 1/(2 : ℝ)) - (1/2 : ℝ) • x.swap
    linear := -(1/2 : ℝ) • {
      toFun := Prod.swap
      map_add' := by simp
      map_smul' := by simp
    }
    map_vadd' p v := by
      simp
      ring_nf
  }
```

After I formalized this, I suspect there is a better method that uses convergence on $`\top \times \mathcal{N}(x)` instead of uniform convergence, since uniform convergence isn't very compositional, whereas continuity on a product filter is more compositional. I have not pursued this properly.

The symmetry properties end up involving some annoying calculation to pick the appropriate $`t_i` so we stay within a quadrant.

```lean notOpen
-- These will all very annoying yet trivial limit calculations
lemma sequence_exists (t : ℝ) (n : ℕ) (h : n/4 ≤ t) (h' : t ≤ (n+1)/4)
 : ∃f : ℕ → ℕ, Filter.Tendsto (fun i ↦ (f i : ℝ) / hilbert_length i) Filter.atTop (nhds t) ∧
  ∀i≥1, n * hilbert_length i ≤ 4*(f i) ∧ 4*(f i) < (n+1) * hilbert_length i := by
  sorry -- it's very long :'(
```

Once we have a bunch of these lemmas for the right sequence and the extra uniform convergence and uniform continuity theorems, we can proceed with stitching it altogether:

```lean openNames
#check limit_hilbert_recurse_bottom_right
/-
The hilbert curve is a fractal just like its construction, i.e.
it can be broken up into 4 copies of itself.
-/
example (t : ℝ) (h : t ∈ Set.Icc (3/4) 1) :
  limit_hilbert_curve t = T3_real_lim (limit_hilbert_curve (4*t - 3)) := by
  rcases (sequence_exists t 3 (by linarith [h.1]) (by linarith [h.2]))
    with ⟨fnat, f_tendsto, hf2⟩
  set f := fun i => fnat i / (hilbert_length i : ℝ) with f_def
  have lhs_tendsto : Filter.Tendsto
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i))
    Filter.atTop
    (nhds (limit_hilbert_curve t)) := by
    apply TendstoUniformly.tendsto_comp (hg := f_tendsto)
    · apply tendstoUniformly_iff_seq_tendstoUniformly.mp
        limit_hilbert_curve_tendstouniformly
      exact Filter.tendsto_add_atTop_nat 1
    exact limit_hilbert_continuous.continuousAt
  have rhs_tendsto : Filter.Tendsto
    (fun i ↦ T3_real i (normalized_hilbert_curve i (4 * f i - 3)))
    Filter.atTop
    (nhds (T3_real_lim (limit_hilbert_curve (4*t - 3)))) := by
    have : Filter.Tendsto (fun i ↦ (normalized_hilbert_curve i (4 * f i - 3)))
      Filter.atTop
      (nhds (limit_hilbert_curve (4*t - 3))) := by
      apply TendstoUniformly.tendsto_comp
      · exact limit_hilbert_curve_tendstouniformly
      · exact Continuous.continuousAt limit_hilbert_continuous
      apply Filter.Tendsto.sub_const
      apply Filter.Tendsto.const_mul
      exact f_tendsto
    apply TendstoUniformly.tendsto_comp
      (hf := T3_real_lim.continuous.continuousAt)
      (hg := this)
      (g := (fun i ↦ (normalized_hilbert_curve i (4 * f i - 3))))
      (h := T3_real_tendsto_uniformly)
  have lhs_eq_rhs :
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i)) =ᶠ[Filter.atTop]
    (fun i ↦ T3_real i (normalized_hilbert_curve i (4 * f i - 3))) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro i ih
    rw [f_def]
    dsimp
    have : get_quadrant i (4*(fnat i)) = Quadrant.BOTTOM_RIGHT := by
      rw [bottom_right_eq]
      exact (hf2 i ih).1
    rw [<-mul_div_assoc]
    rw [normalized_recurse_bottom_right this]
    have : ((4 : ℝ) * fnat i - (3 : ℝ) * (hilbert_length i)) / ↑(hilbert_length i) =
      (4 : ℝ) * fnat i / (hilbert_length i) - (3 : ℝ) := by
      have := hilbert_length_pos i
      field_simp; ring
    rw [this]
  rw [Filter.tendsto_congr' lhs_eq_rhs] at lhs_tendsto
  apply tendsto_nhds_unique lhs_tendsto rhs_tendsto
```

I only did the bottom left and bottom right case, because that's sufficient to prove it isn't injective. That proof in particular is a bit boring.

# {label additionaldirections}[Additional Directions]

Like every formalization project, it ends up being a lot more than you expect. Not only was it more involved, technical, time-consuming, and plain difficult, but it was also more rewarding. I have run out formalization steam, so these will remain informal until AI takes over or whatever. By the end, I had a lot better grasp on some more non-trivial facts:

I would consider any one of these to be a pretty decent puzzle.

## {label symmetry}[Symmetry]

After thinking about the symmetry relations of the Hilbert curve, I realized:

**Any function satisfying the same symmetry law is the Hilbert curve**.

Suppose you have some $`t \in [0, 1]`. This $`t` is in one of 4 quadrants, $`[0, \frac{1}{4}]`, $`[\frac{1}{4}, \frac{1}{2}]`, etc. We know that transformation symmetry applies on each quadrant, and it matches at each boundary. Our symmetry also tells us that $`f(t)` lies in that smaller square as long as it lies in $`[0, 1] \times [0, 1]`. Each iteration, additional information from $`t` reduces this square to a square with $`\frac{1}{2}` the size. At this point, we have a sequence of nested squares. We can pick a point from each square and use the completeness of $`\mathbb{R} \times \mathbb{R}`, or we can intersect the sequence of compact sets using Cantor's intersection theorem to get a point in the limit.

Any uniform collection of contractions will eventually converge to a point like this, so our assumption that $`f(t) \in [0, 1] \times [0, 1]` or that these are squares is unnecessary.

## {label holder}[Hölder continuity]

Early on, I wanted to hope that the final curve was Lipschitz or something, but a simple estimate suggests that any bound will get broken as you $`\tilde{H}_i(t)` speeds up by a factor of $`2` each iteration at $`t = 0`. However, I know from the Cauchy bound that it doesn't get _too_ far away. As each iteration divides a segment into segments 1/4 the size that move 1/2 as far, this suggests that we are looking for a square-root.

This immediately suggests (to me) that we use Hölder continuity

$$`
\lVert f(t) - f(s) \rVert \le C \lVert t - s \rVert^\alpha
`

where $`\alpha = \frac{1}{2}`.

We can do some plots (in Lean of course) to validate the exact the constant.

::::blob displacement_plot
::::

I tested different values until $`C = 2` looked appropriate when I increased the iteration. I suspect this proof is just another tedious application of each transformation, so I leave it up to anyone else to prove this.

It turns out any Hölder continuous map from a set $`s` with exponent $`1/d` can have dimension at most $`d \, \mathrm{dim}\, s`, so in our case, we know that since the image of the Hilbert curve has dimension 2, then it can't be Hölder continuous with exponent $`> 1/2`, and in particular, it can't be Lipschitz or differentiable.

Oddly enough, this fact actually IS in Lean already!

## {label lsystems}[L-Systems]

The symmetry structure plus making sure everything connects up seems like it is actually sufficient for continuity, so there may be some related facts that show that any L-system satisfies some nice continuity relations. I suspect the "space-filling" depends on the exact fractal nature of those systems.

I never proved that the [L-system definition](https://en.wikipedia.org/wiki/Hilbert_curve#Representation_as_Lindenmayer_system) is equivalent, and it looks like once again, annoying induction.

## {label base4}[Base-4 Representation]

The symmetry section should also hint that we can look at the curve as splitting a base-4 number into 2 base-2 numbers.

Each digit tells you which quadrant you are in, so define the digits of the base-2 numbers:

- 0.0... -> (0.0..., 0.0...)
- 0.1... -> (0.0..., 0.1...)
- 0.2... -> (0.1..., 0.1...)
- 0.3... -> (0.1..., 0.0...)

I know that the continuity conditions here amount to any Gray code. The flipping and swapping are still necessary and involve dealing with the digits in a different way depending on earlier digits, but this doesn't appear to be anything more than a technical obstacle.

## {label partialinverse}[Partial Computable Inverse]

The symmetry-based algorithm not only gives a computable definition for $`\mathbb{R} \to \mathbb{R}`, but it and the injectivity arguments also suggest that there is a partial computable inverse:

When we proved the function is not-injective, we had to pick some inputs which mapped to the boundary $`\{\frac{1}{2}\} \times [0, \frac{1}{2}]`. These are in fact the only places where it is not injective. If $`(x, y)` has irrational coordinates, then each time we ["coinduct"](https://en.wikipedia.org/wiki/Coinduction) and break it down into sections, we get a unique quadrant like $`t \in [\frac{1}{4}, \frac{1}{2}]`. Since this is unique every time, we can get a series of increasing approximations like before, and find the unique $`t` such that $`H(t) = (x, y)`.

I'd also like to thank Sam Sartor for first pointing out to me these "grids" fill up the space in a weird way. I guess it was relevant later.

From here, we can refine our surjectivity in a nice way, there is a computable left-inverse on all but a dense set of measure $`0`.

## {label rationals}[Hilbert Curve on the Rationals]

$$`H(\mathbb{Q}) \subseteq \mathbb{Q} \times \mathbb{Q}`

Once I saw the symmetry relations, the digits definition, and I computed a few $`H(t)` "by hand" for a version of the non-injectivity theorem, I realized there was a "sharper" computable algorithm for $`H`.

As an example, let's do $`\frac{1}{3}`, which is how I got into this. By inspecting $`\frac{1}{3} = \frac{1}{4} + \frac{1}{4}\frac{1}{3}`, we know that each iteration, we zoom into the top left corner, and when we do $`4 (\frac{1}{3} - \frac{1}{4}) = \frac{1}{3}` . This gives us a single transformation: zoom in up and to the left each time. This gives a sequence $`\frac{1}{2} + \frac{1}{4} + \cdots = 1` for the $`y`-coordinate and $`0` for the $`x`-coordinate. Thus $`H(\frac{1}{3}) = (0, 1)`.

Suppose we expand $`t \in \mathbb{Q}` into an its base-4 representation: $`t = 0.t_1 t_2 t_3 \cdots`. Eventually, this expansion starts repeating, say at digit $`n + 1` to $`n + T`.  The first $`n` digits will localize us to some smallish square, and then we'll explicit calculate $`H(t)` for some $`t` which _immmediately_ repeats.

For repeating digits $`0.t_1 \cdots t_T t_1 \cdots`, we can construct a function $`T_{t_1 t_2 \cdots t_T}` which zooms into the appropriate section, which we can iterate to get out final output as the final fixed point. This function $`T` is an affine map, which can be explicitly computed. Since the fixed points of affine maps can be solved for using linear algebra (i.e. $`A x + b = x` is a linear equation), we can solve the appropriate matrix, and then find $`H(t)` without looking at all the digits.

Combining this with our other transformation gives us $`H(t)` for any rational $`t`. Since every transformation here involves rational matrices and solving a rational linear system, we can compute an rational inverse matrix and thus $`H(t) \in \mathbb{Q}`.

I would be interested to learn a proof of this fact which isn't constructive.

## {label mathlib}[Mathlib additions I would like to do]

There's some instances I just don't understand the implications of like casting products and OrderedRing on products.

I would like to add a few lemmas about limits of floors and floor of integer division, which seem easy enough.

Interpolation has _too many_ extensions, so requires more thought, particularly in regards to complex analysis.

Finally, continuous affine maps are a bit of frustration to work with. Once topological vector spaces are in, then we'll have the unfortunate problem of transferring everything from there to continuous affine maps too, which involves picking a zero over and over again. Right now, the normed continuous affine maps are the only nice ones.

# {label proscons}[Pros and Cons of using Lean here]

Overall, I'm pretty happy I did this formalization. Formalization really pushes you in a way that writing sometimes doesn't. I would suspect that I could have gotten 80% of the insight with 20% of the effort if I actually wrote a blueprint out first, whoops. The computation and casework seems to still be a bit of a nightmare, and in this case, I'm not sure what could really make that part "pleasant". There's a lot of geometric intuition.

Using ProofWidgets was a great idea, since it caught bugs I would have needed some serious formalization to uncover, such as _during_ proving injectivity. I was surprised at (1) how easy it is for AI to autogenerate these and (2) how difficult it was to just write JavaScript mself. It's obvious that ProofWidgets is just injecting JavaScript, but Lean makes string-interpolating your own JavaScript indirect. I actually regret not using ProofWidgets more by substituting specific examples when I am doing algebra. The only big impediment is that $`\mathbb{R}` is usually noncomputable, and producing a useful approximation requires "breaking" out of a quotient, so it's usually easier to build out numeric testing separately for $`\mathbb{R}`.

"When I tried to use any sort of AI, it usually failed. There was a few really early, basic definitions for the different transformations which Gemini 2.5 did quite well on. It did great on SVG generation and JavaScript. However, the moment you had a mildly complicated proof like "interpolation is continuous", then even the super fancy "DeepSeek-Prover-V2" got stuck in a loop trying to prove $`t - \lfloor t \rfloor` is continuous. Even when they did work, they often produced some of the ugliest proofs I've seen in my life, and it was faster to rewrite them from scratch then clean it up. Many of the provers are trained using only pretraining + pure RL, so they don't look up theorems when they should, they write 10 different tactics in a row and hope it works, they are incapable of running Lean code while generating, they can't simplify or take wrong paths, so overall they end up completely useless for even the amateur mathematician.

`mathlib`'s continuous affine map situation cost me a week of reading 3 or 4 inconsistent versions of the APIs I needed. I do hope they fix it (if they haven't already). I still suspect that uniform continuity isn't well-adapted for filters.

# {label conclusion}[Conclusion]

The Hilbert curve has some nice properties in both the integers and the reals, and in my opinion, any finite integer implementation is only correct because of the convergence to the reals. That makes it an interesting verification exercise, since you can't really avoid having to deal with limits. There are plenty of other similar pathological curves with similar constructions (like [Whitney's "A function not constant on a connected set of critical points"](https://www.mimuw.edu.pl/~pawelst/am2/Analiza_Matematyczna_2/Notatki_files/Przyk%C5%82ad_Whitneya.pdf)). I've purposefully ignored looking too hard into the literature here, since I wanted to learn from formalization instead of just formalizing known facts. Even now, I am wary of letting go of some puzzles and looking up an answer.

Ultimately, I am getting bit tired of these kind of obvious tasks becoming a 3000 LOC adventure. Frankly, many days weren't enjoyable, and I do this primarily because I find it fun. At some point, I would like to play around with something less obvious and less verbose instead, or at least on work on tackling these usability problems instead of suffering through them. There's plenty of things to work on still.

# {label verso}[P.S. Verso is fine]

I wrote this blog post by drafting first in Obsidian, and then copying it to [Verso](https://github.com/leanprover/verso).

I don't know if I've gotten better at Lean or if Verso has gotten easier to use, but I needed a lot less boilerplate to get this blog-post in Verso. I have a few notes at https://github.com/josephmckinsey/HilbertCurveBlogPost/blob/main/notes for some of the problems I encountered, but overall I feel like I have a real template for next time here.
