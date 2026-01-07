## 1. Define the exact target and what “improving the constant” means

Fix a hull size parameter (h = O(1)). For each (n), consider the minimum over all (n)-point sets (P \subset \mathbb R^2) with (|\mathrm{CH}(P)| = h) of
[
pg(P) = #{\text{plane graphs on }P}.
]
The goal is a bound of the form
[
pg(P) \ge c^n \cdot \text{poly}(n)^{-1}
]
uniformly over all such (P). Improving the lower bound means increasing the exponential base (c).

In this line of work, (c) is almost always determined by a single “rare feature” inequality, which bounds the expected count of some removable local structure in a uniform random plane graph.

So the project reduces to identifying a removable structure with a provably small expected frequency, then converting that into a multiplicative recurrence for (pg(P)).

---

## 2. The core counting reduction that turns expectation bounds into (c^n)

### 2.1 Pick a removable object type (R)

Examples:

* an isolated interior vertex
* an interior vertex of degree 1 with a forced neighbor
* a small “removable gadget” that can be deleted while preserving planarity and the hull condition

The removable type must have two properties.

**Deletion property.** If (G) has a removable object at vertex (p), then deleting (p) (and some incident edges if needed) gives a plane graph on (P \setminus {p}) that stays inside the same class you want to recurse on.

**Controlled reinsertion property.** For any graph (H) on (P \setminus {p}), the number of ways to reinsert (p) to create a valid (R)-object in a graph on (P) is at most (K), where (K) is a constant that you can bound cleanly.

For isolated vertices, (K = 1). For richer removable patterns, (K) might be 2, 3, 8, and so on.

### 2.2 Convert “few (R)-objects in expectation” into a recurrence

Let (G) be uniform over all plane graphs on (P). Let (X_R(G)) be the number of removable objects in (G).

If you can prove, for every eligible (P),
[
\mathbb E[X_R(G)] \le \delta n,
]
then a double counting argument on pairs ((G, \text{choice of a removable object in }G)) typically yields something of the form
[
pg(P) \ge \frac{1}{K\delta}, \sum_{p \in P'} pg(P\setminus{p}),
]
where (P') is the subset of points whose deletion preserves the hull condition (often “interior points” when hull size is fixed).

When the class is stable under deletion of interior points, this becomes a clean recurrence like
[
pg_h(n) \ge \frac{1}{K\delta}, pg_h(n-1),
]
so
[
pg_h(n) \ge \left(\frac{1}{K\delta}\right)^{n-O(1)}.
]

**Key takeaway:** the exponential base is essentially
[
c \approx \frac{1}{K\delta}.
]
To improve (c), reduce (\delta), reduce (K), or both.

This is the main lens for all improvements.

---

## 3. The probabilistic object that makes the analysis feasible

The analysis is done under the uniform distribution on plane graphs on a fixed point set (P).

You rarely try to compute (\mathbb E[X_R]) directly. Instead, you upper bound it using a charging identity that converts an expectation question into a deterministic inequality that holds for every graph.

That is where cross-graph charging enters.

---

## 4. Cross-graph charging as an expectation upper bound machine

### 4.1 Package vertex local states as “vings”

A “ving” is a pair ((p, G)) where (p \in P) and (G) is a plane graph on (P).

You define a local parameter of ((p,G)) that controls how many graphs can be formed by adding edges incident to (p) without crossings. Typical choices:

* degree of (p) in (G)
* “visibility count” from (p) in (G)
* “potential” = degree plus visibility, or another monotone proxy

### 4.2 Define a family over graphs via adding incident edges at (p)

Fix (G) and (p). Consider the set of graphs obtained by adding any subset of visible noncrossing edges incident to (p). This is a family of size (2^j) where (j) is a local visibility parameter.

This is the cross-graph connection. A single ving touches many graphs.

### 4.3 Create an invariant: total charge summed over all graphs

The standard pattern:

1. Assign an initial charge to each ving, often depending only on degree, or on a small local type.
2. Push charge across graphs within the family so that the final charge of each ving becomes a simple function like (2^{-j}).
3. Because this redistribution is within families, the total charge summed over all vings over all graphs is unchanged.

Then,
[
\mathbb E[\text{something}] = \frac{1}{pg(P)} \sum_{G} \sum_{p} \text{indicator or weight at }(p,G)
]
can be bounded by relating that indicator to final charge.

The endgame is always the same:

* Show that the total final charge inside any fixed graph (G) is at most (C n + O(1)).
* Conclude that the expectation of the targeted feature is at most (C n / pg(P)) in the appropriate normalized way.
* Translate to (\delta).

### 4.4 What actually governs the constant (C)

At the end you typically need a worst case bound on something like
[
\sum_{p \in P} 2^{-\mathrm{pt}(p,G)}
]
or a small variant.

So improving the lower bound is mostly about forcing that sum to be smaller in every graph when the hull size is constant.

---

## 5. Where “constant hull size” should enter the proof

Constant hull size gives two kinds of leverage.

### 5.1 Almost all vertices are interior

Only (h = O(1)) vertices lie on the hull. Any argument that separates hull vertices from interior vertices can treat the hull contribution as (O(1)) or (o(n)).

This matters because the recurrence wants deletions that preserve hull size, which is usually guaranteed by deleting interior vertices.

So a good setup is:

* define the removable feature only for interior vertices
* prove an expectation bound for interior vertices only
* ignore hull vertices as lower order terms

### 5.2 Triangulations have almost fixed edge counts

Any plane graph can be extended to a triangulation by adding noncrossing edges. In a triangulation with hull size (h),

* edges are (3n - 3 - h)
* degree sum is (6n - 6 - 2h)

When (h) is constant, these are (3n - O(1)) and (6n - O(1)).

This lets you add strong constraints on possible degree distributions in triangulations, and then lift those constraints back to your charge bound, because potential is usually lower bounded by a triangulation degree or something comparable.

That is why many proofs end up needing lemmas that bound how many vertices can have degree 3, 4, and so on.

---

## 6. The three main routes to increasing the exponential base

### Route A: Improve (\delta) for the same removable feature

This means tightening the charging analysis so the worst case total charge per graph drops.

Typical tactics:

1. **Refine types.** Instead of one charge per degree, split by interior versus hull, or split by visibility class, or split by face patterns around the vertex.
2. **Second-stage recharging.** After the main family averaging, add a deterministic within-graph discharging step that moves charge away from the worst offenders (usually the smallest potentials).
3. **Use additional hard constraints in the final maximization.** The last step is often an extremal optimization over possible local statistics. If it ignores a valid constraint, the constant is leaving slack on the table. For hull-constant triangulations, the degree sum constraint alone can tighten that optimization.

This route usually yields incremental gains, but it is the most reliable.

### Route B: Keep the same charging tools but choose a better removable feature

Isolated vertices are convenient because reinsertion has (K=1), but they might not be the best choice.

A stronger approach is to count a feature that is still rare, but whose deletion creates more reinsertion options. If deletion has at most (K) reinsertion choices, then (c \approx 1/(K\delta)). If (\delta) drops by a factor larger than (K) rises, you win.

Good candidates are local configurations that are:

* interior
* recognizable from a bounded neighborhood
* preserved under triangulation extension or visibility reasoning
* easy to reinsert with few choices

This route can create larger jumps in (c), but it takes more design work.

### Route C: Combine multiple removable features into one recurrence

Instead of relying on only one feature, you can prove that every graph has many vertices that fall into at least one of several removable types (R_1, R_2, \dots), and control the reinsertion multiplicities.

A clean way is to define a random variable that is a weighted sum:
[
X(G) = \sum_i \alpha_i X_{R_i}(G)
]
and prove (\mathbb E[X(G)] \le \delta n), then choose weights to optimize the best recurrence.

This naturally becomes a linear optimization problem, which is ideal for certificate-driven workflows.

---

## 7. Turn “proof search” into “optimize a certificate” using computation

A practical way to build improvements that are both real and checkable is to formalize the charging argument as a finite system of linear inequalities.

### 7.1 Express the charging scheme with finitely many local states

Pick a finite list of local configuration types that cover everything you use in the proof. Examples:

* degree in triangulation in ({3,4,5,6,\ge 7})
* whether the vertex is on the hull
* whether the vertex is in a “bad” face pattern

Then your charging scheme assigns:

* initial charge values to each type
* transfer rules that are local and type-based

### 7.2 Correctness becomes linear constraints

For each configuration type, constraints enforce:

* charge conservation across the cross-graph families
* nonnegativity
* that final charge upper bounds the indicator of the removable feature you care about
* any geometric constraints you have proved about counts of certain types

### 7.3 The objective is the final constant

You optimize the bound on total charge per graph, which implies a bound on (\delta), which implies (c).

This optimization can be solved in rational arithmetic or solved approximately then rounded to rationals.

### 7.4 Export a machine-checkable certificate

The certificate should contain:

* the type system
* the chosen rational parameters
* the derived inequality in an explicit algebraic form

Then a verifier checks each inequality step using exact rational arithmetic.

This is the cleanest loop for rapid iteration.

---

## 8. Role separation: mathematics, search, and formal verification

A robust structure is to split the work into three layers that interact tightly.

### Layer 1: Human mathematics

* define the removable feature and reinsertion bound (K)
* define the vings, families, and potential
* prove the geometric constraints and combinatorial inequalities that are not purely numeric
* prove the reduction from expectation bound to the recurrence

These are the parts where new ideas usually appear.

### Layer 2: Computational exploration and optimization

* generate candidate worst-case point sets for small (n)
* test candidate constants against exact enumeration for small (n)
* solve the linear optimization for the best parameters
* produce certificates and counterexamples

This layer tells you where the bottleneck is.

### Layer 3: Formal verification

* encode definitions precisely
* verify every inequality and the logical chain from certificate to (\delta) to (c)
* record explicit small (n) exceptions and prove them as needed to make the asymptotic statement correct

This layer prevents hidden mistakes and makes iteration safe.

---

## 9. A concrete milestone plan that steadily improves the bound

### Milestone 0: Reproduce the current bound end to end

* verify the recurrence statement and which vertex deletions preserve hull size
* verify the charging identity and the per-graph total charge bound
* confirm small (n) behavior and record exceptions

This ensures the pipeline is correct.

### Milestone 1: Remove slack in the final optimization

* rewrite the last “worst case charge” step as an explicit optimization problem
* include every valid constraint that comes from hull size being constant
* compute the tightest constant for the existing scheme

This often yields a free improvement.

### Milestone 2: Add one refined local parameter

* split hull versus interior
* or split one degree bucket into two
* or add a simple face-pattern flag

Re-optimize and see if the constant moves. If it does, the bottleneck is sensitive and further refinement is likely productive.

### Milestone 3: Add a second-stage recharging targeting the worst offenders

* identify the local types that dominate the optimized worst case solution
* design a deterministic discharging rule that reduces their final charge without increasing others too much
* re-optimize and certify

This is a common way to break through a plateau.

### Milestone 4: Experiment with a new removable feature with small (K)

* define the deletion and reinsertion map
* prove the map is valid for all point sets with hull size (h)
* build the charging scheme to bound its expected frequency
* optimize and certify

This is the route that can yield the largest jump when the isolated-vertex approach hits a ceiling.

---

## 10. A good mental model for “what to try next”

When the bound is stuck, ask which of these is true.

1. The worst case comes from too many vertices of one low potential type.
   Then refine types and add a recharging step that penalizes that type.

2. The worst case comes from the proof allowing impossible global statistics.
   Then add constraints that must hold in triangulations with constant hull size, especially degree-sum and any proven limits on degree 3 and 4 frequencies.

3. The removable feature is fundamentally too weak.
   Then switch to a feature that still recurses cleanly, but is rarer or has a better (1/(K\delta)) tradeoff.

That is the overall framework. It gives a repeatable loop where each iteration either produces a certified improvement, or identifies the exact structural lemma that would be needed to improve further.
