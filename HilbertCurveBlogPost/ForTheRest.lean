import VersoBlog
import HilbertCurveBlogPost.CommonElements
import HilbertCurve

open Verso Genre Blog
open Verso.Doc

set_option pp.rawOnError true

-- I removed some definitions, and now this is necessary...
set_option maxHeartbeats 800000

#doc (Page) "Hilbert Curves" =>

> "Everyone understands what a curve is, until they study enough math to become confused." -- Matt Iverson's friend from highschool?

In the limit, the Hilbert curve is a weird fractal that curves around to completely fill up a square $`[0, 1] \times [0, 1]`. To those who haven't internalized analysis, a full informal proof may scare one by referencing uniform convergence and Cauchy sequences, but I hope the gist is understandable enough. Given that correctness of the Hilbert curve requires such depth, it seemed like a good test case to formalize in the programming language [Lean](https://lean-lang.org), so we can see the difference in theory vs application.

::::blob hilbert_curve_123
::::

Below, I'll go through the definitions and some informal proofs of the Hilbert curve. For those familiar with Hilbert curves or only interested in Lean, please skip to the [next post](https://josephmckinsey.com/leanhilbertcurves.html), where I present portions of the [full formalization](https://github.com/josephmckinsey/LeanHilbertCurves).

If a weird curve that appears two-dimensional isn't interesting or pathological enough for you, the discrete versions by themselves are quite useful. They provide a continuous mapping of integers to 2D coordinates which is pleasant when giving a 1D coordinate for the Earth in [S2 Geometry](http://s2geometry.io/),  or visualizing [ISBNs](https://phiresky.github.io/blog/2025/visualizing-all-books-in-isbn-space/) and [IP addresses](https://davidchall.github.io/ggip/articles/visualizing-ip-data.html).

# {label definition}[The Definition of the Hilbert Curve]

First, we're going to go through definitions, which constitute all you need for plotting and visualization. Unlike most mathematical objects, their properties can be revealed succinctly through drawings and a few sentences. After that, some proofs.

## {label integerdefinition}[Integer Version]

**Informal Definition**: The 0th Hilbert curve is the constant $`(0, 0)`. To construct the $`n`th Hilbert curve, take 4 copies of the $`(n-1)`th Hilbert curve and stitch them together. To show the transformations more clearly, we'll draw the $`(n-1)`th iteration more abstractly as a shape:

::::blob hamster_alone
::::

where we start at $`(0, 0)` and end on the right. Then we'll assemble them as in the diagram below:

::::blob hamster_together
::::

I tend to think of the integer Hilbert curve as little blocks instead of tiny curves, so we can diagram them as a sequence of colored squares:

::::blob hilbert_curve_red_squares
::::

**Formal Definition**: On the integers, we'll define a Hilbert curve $`H_n : \mathbb{N} \to \mathbb{N} \times \mathbb{N}` recursively as follows.
1. $`H_0(i) = (0, 0)`.
2. $$`H_n(i) = \begin{cases}
	swap(H_{n-1}(i)) &\text{ if } i < 2^{2(n-1)} \\
	H_{n-1}(i - 2^{2(n-1)}) + (2^{n-1}, 0) &\text{ if } 2^{2(n-1)} \le i < 2 \cdot 2^{2(n-1)} \\
	H_{n-1}(i - 2 \cdot 2^{2(n-1)}) + (2^{n-1}, 2^{n-1}) &\text{ if } 2 \cdot 2^{2(n-1)} \le i < 3 \cdot 2^{2(n-1)} \\
	(2^n - 1, 2^{n-1} - 1) - swap(H_n(i - 3 \cdot 2^{2^(n-1)})) &\text{ if } 3 \cdot 2^{2(n-1)} \le i
   \end{cases}`
   where $`swap((m, n)) = (n, m)`.

We will focus on the first $`2^{2 n}` indices on the curve, which fill up a grid from $`[0, 2^n) \times [0, 2^n)`. From the picture, it's clear that no two indices go to the same square on the grid.

## {label normalizeddefinition}[Normalized and Interpolated Version]

We can also interpolate and rescale each iteration to get a different kind of picture.

**Informal Definition**: We interpolate the $`n`th Hilbert curve to get a curve $`\mathbb{R} \to \mathbb{R}`, then we scale the down the input by $`\frac{1}{2^{2n}}` so it goes from $`[0, 1]`, then we scale down the output by $`\frac{1}{2^n}` so it fits in $`[0, 1] \times [0, 1]`.

Now, our pictures will look like the more recognizable (to some) Hilbert curve:

::::blob hilbert_curve_3
::::

**Formal Definition**: The normalized Hilbert curve $`\tilde{H}_n : \mathbb{R} \to \mathbb{R}` is defined as
$$`\tilde{H}_n(t) = \frac{1}{2^n} \left( (t \cdot 2^{2n} - \lfloor t \cdot 2^{2n} \rfloor) H_n(\lfloor t \cdot 2^{2n} \rfloor + 1) + (1 - t \cdot 2^{2n} + \lfloor t \cdot 2^{2n} \rfloor) H_n(\lfloor t \cdot 2^{2 n} \rfloor) \right)`
Alternatively, if $`L(x, y, t) = (1 - t) x + t y`, then
$$`\tilde{H}_n(t) = \frac{1}{2^n} L(H_n(\lfloor t \cdot 2^{2 n} \rfloor), H_i(\lfloor t \cdot 2^{2 n} \rfloor + 1), t \cdot 2^{2 n} - \lfloor t \cdot 2^{2 n} \rfloor)`
From our pictures, it's also clear that the curve is not only continuous, but each iteration doesn't move that much from the previous--$`H_n(i)` is only one block off from $`H_i(i + 1)`.

## {label limitdefinition}[Limit version]

The Hilbert curve iterations also satisfy an important property that we need for the next definition. Each time we iterate, we "refine" the Hilbert curve.

**Informal Lemma**: If you are in a square of the old Hilbert curve, then the next iteration only splits that square, so you'll remain there in future iterations.

From our colorful picture before, the color represented the position in the sequence, so this translates to iterations mostly preserving color:

::::blob hilbert_curve_rainbow2
::::

::::blob hilbert_curve_rainbow3
::::

This also applies to the normalized version. Now $`\tilde{H}_n(t)` is close to $`\tilde{H}_{n+1}(t)`, and each iteraiton brings them closer and closer as the Hilbert curve squares decrease in size.

::::blob hilbert_curve_comparison34
::::

Now we get our limit:

**Definition**: Let $`H(t) = \lim_{n \to \infty} \tilde{H}_n(t)`.

Unfortunately, our picture is somewhat less interesting from a visual perspective, but more interesting from a mathematical perspective:

::::blob a_big_square
::::

Here's the interesting thing about the Hilbert curve: it's a _space-filling curve_, which means it's not only still continuous, but fills the region $`[0, 1] \times [0, 1]`. This is surprising because curves are famously one-dimensional. Luckily for us, every mathematical pathology is actually a mathematical opportunity.

# {label informalproofs}[Informal Versions of Formalized Theorems and Proofs]

Unless stated otherwise, $`\lVert (x, y) \rVert = \mathrm{max}(|x|, |y|)`. These proofs will not be detailed enough usually to serve as a blueprint for Lean. It is meant to be read and clarify the Lean code later. Most of the details are too boring and uninteresting.

## {label informalintegers}[Integer Facts]

**Lemma**: The integer Hilbert curves maps $`[0, 2^{2 n} - 1]` precisely onto $`[0, 2^n -1] \times [0, 2^{n} - 1]`.

For this, we can check that each transformation in the definition maps to each quadrant, then we can use induction to prove that it's injective (also known as [one-to-one](https://en.wikipedia.org/wiki/Injective_function)). Surjectivity follows from the finite domain. $`\blacksquare`

**Lemma**: The integer Hilbert curves never move by more than one, so $`|H_n(i+1) - H_n(i)|_1 = 1`.

Try induction and note that each transformation lines up the end of the Hilbert curve at the start of the previous. $`\blacksquare`

**Lemma**: The integer Hilbert curves "refines" each square, so $`H_{n+1}(i) \in [2 H_n(\lfloor i / 4 \rfloor), 2 H_n(\lfloor i / 4 \rfloor) + 1]`.

Try induction and case work on the quadrants, it really boils down to algebra for each square. $`\blacksquare`.

We could also build on this to show that $`H_{n+m}` will always remain in that square, but we will not need that later, so I'll avoid it.

## {label normalizedproofs}[Normalized and Interpolated facts]

From those, we can get some also nice facts about the interpolated version:

**Lemma**: The normalized Hilbert curves is contained within $`[0, 1] \times [0, 1]`.

This is basic algebra. $`\blacksquare`

**Lemma**: They "almost" fill up the space, so for all $`x \in [0, 1] \times [0, 1]`, there is a $`t \in [0, 1]` such that $`\lVert \tilde{H}_n(t) - x \rVert \le \frac{1}{2^n}`.

First we take $`x`, then find a nearby pair of integers $`\le \frac{1}{2^n}` away, and finally we use our integer Hilbert curve to find the corresponding $`n` from which we get $`t` via scaling. $`\blacksquare`

**Lemma**: The Hilbert iterations get close together, so $`\lVert \tilde{H}_{n+1}(t) - \tilde{H}_{n}(t) \rVert \le \frac{2}{2^n}`. This constant in the numerator can probably be lowered, but I haven't checked exactly how far.

Since I want to avoid casework as much as possible, the easiest way to prove this seems to construct a chain of approximations instead:
$$`
\begin{align*}
\lVert \tilde{H}_{i+1}(t) - \tilde{H}_{i}(t) \rVert &\le
\lVert \tilde{H}_{i+1}(t) - \tilde{H}_{i+1}(\lfloor t \cdot 2^{2(n+1)} \rfloor / 2^{2 n}) \rVert \\
&+ \lVert \tilde{H}_{i+1}(\lfloor t \cdot 2^{2n} \rfloor / 2^{2(n+1)}) - \tilde{H}_{i}(\lfloor t \cdot 2^{2n} \rfloor / 2^{2 n}) \rVert \\
&+ \lVert \tilde{H}_{i}(t) - \tilde{H}_{i}(\lfloor t \cdot 2^{2n} \rfloor / 2^{2 n}) \rVert
\end{align*}
`
The first can be bounded by $`\frac{1}{2^{n+1}}` since our interpolation only moves $`\frac{1}{2^{n+1}}` between each corner, and similarly by $`\frac{1}{2^n}` for the third case, the second can be bounded by $`\frac{1}{2^{n+1}}` using the square containment lemma from the integer case.

This lemma can also be improved by using the fact that $`\tilde{H}_{n}((i + 1) / 2^{2 n})` is still in the same square as $`\tilde{H}_n(i  / 2^{2 n})`, but in the moment of formalization, it was more convenient to use the distance lemmas instead. $`\blacksquare`

## {label limitproofs}[Limit Facts]

Now we can get to fun stuff:

**Theorem**: The limit $`H(t)` is continuous.

The crucial part here is [uniform convergence](https://en.wikipedia.org/wiki/Uniform_convergence), which means that $`\tilde{H}_n`'s rate of convergence is the same everywhere, which will preserve continuity in our limit. For each $`n`, we have that $`\lVert \tilde{H}_n(t) - \tilde{H}_{n+1}(t) \rVert \le \frac{2}{2^n}`, then
$$`
\lVert \tilde{H}_n(t) - H(t) \rVert \le \sum_{i=n}^\infty \lVert \tilde{H}_i(t) - \tilde{H}_{i+1}(t) \rVert \le \sum_{i=n}^\infty \frac{2}{2^i} = \frac{4}{2^{2 n}}.
`

So thus, $`\tilde{H}_n(t)` converges uniformly to $`H`, since this bound doesn't depend on $`t` at all. Therefore by the [Uniform Continuity Theorem](https://en.wikipedia.org/wiki/Uniform_limit_theorem), $`H` is continuous since each $`\tilde{H}_n` is continuous. $`\blacksquare`

**Theorem**: The limit $`H(t)` maps $`[0, 1]` onto $`[0, 1] \times [0, 1]`.

Let $`x \in [0, 1] \times [0, 1]`. Next, we will find a sequence of $`t_i` that converge to some $`t` such that $`\tilde{H}_i(t) \to x`. Finally, since $`\tilde{H}_i` converges uniformly, then $`\tilde{H}_{i}(t) \to H(t) = x`.

Since $`[0, 1]` is [sequentially compact](https://en.wikipedia.org/wiki/Sequentially_compact_space), it suffices to find any sequence $`t_i` such that $`\tilde{H}_i(t_i)` converges to $`x`, so then a subsequence of $`t_i` will truly converge to a $`t`. Using our approximate inverse property from before, we can always pick a $`t_i` such that $`\lVert \tilde{H}_i(t_i) - x \rVert \le \frac{1}{2^n}`. As $`\frac{1}{2^n}` converges to $`0`, thus $`\tilde{H}_i(t_i)` converges to $`x`. So thus, our convergent subsequence also converges to $`x` and $`H(t) = x`. $`\blacksquare`

This completes the usual standard set of facts (such as most of Munkres' Topology). We see that $`H` cannot be injective, since any continuous injective map is a [homeomorphism](https://mathworld.wolfram.com/Homeomorphism.html) onto its image, and $`[0, 1]` is not homeomorphic to $`[0, 1] \times [0, 1]`. Unfortunately, this fact is not in Lean's [mathlib](https://github.com/leanprover-community/mathlib4) (the library of available theorems for later), and likely never will be, since you really want that $`\mathbb{R}^n \not\cong \mathbb{R}^m` for $`m \neq n` which goes by [invariance of domain](https://en.wikipedia.org/wiki/Invariance_of_domain) and is a standard result from algebraic topology. I could not find this in Lean, but maybe I was missing something. However there is another more rewarding route: symmetry arguments!

**Theorem**: The limit $`H` is symmetric in a similar way to the integer case.

Although the normalized interpolated $`\tilde{H}_i(t)` is not _precisely_ symmetric, we can use the same trick as before and pick a sequence $`t_i` on the corners that exactly matches the symmetry transformations we do have. Our symmetries are also now much simpler, since we can use $`1` and $`\frac{1}{2}` instead of $`2^n` and $`2^{n-1}`. Since our symmetries are [uniformly continuous](https://en.wikipedia.org/wiki/Uniform_continuity), we still get uniform convergence and the sequence limits passes through the convergence still.

I will not spell out the rest of the details here, since the algebra is relatively unenlightening. $`\blacksquare`

**Theorem**: The limit $`H` is not injective.

Since $`H` is symmetric, we can look at the bottom left quadrant and the bottom right quadrant and see that they overlap at the boundary $`\{\frac{1}{2}\} \times [0, \frac{1}{2}]`. Since $`H` is symmetric and surjective, there is a $`t \in [0, \frac{1}{4}]` (the bottom left quadrant) such that $`H(t) = (\frac{1}{2}, 0)`. Similarly there is a $`t \in [\frac{3}{4}, 1]` (the bottom right quadrant) such that $`H(t) = (\frac{1}{2}, 0)`. These $`t`s have to be different, so thus $`H` is not injective. $`\blacksquare`

These is the end of what I've formalized in Lean, but once you've thought about every detail so much for so long, additional properties become fairly clear too. If you aren't interested in Lean, you may find all those of interest in the [next post](https://josephmckinsey.com/leanhilbertcurves.html).

# {label conclusion}[Conclusion]

Hopefully, you've learned that the Hilbert curve is a continuous curve that looks like a square. That's the main cool fact about Hilbert curves.

# {label references}[References]

I only looked at Wikipedia and Munkres' Topology section "A Space-Filling Curve" (Chapter 7, section 44).
