Here’s the clean picture.

Take (k\ge 3) and put
[
q:=k-1.
]

In the usual block encoding, a word (x=x_1\cdots x_n\in [q]^n) represents the (n)-set
[
S(x):={(1,x_1),\dots,(n,x_n)}.
]
Then every (q)-ary language is automatically (k)-sunflower-free: if (S(x^{(1)}),\dots,S(x^{(k)})) were a sunflower, then at every coordinate outside the core the (k) petals would force (k) distinct symbols, impossible over an alphabet of size (q=k-1).

So in the finite-state (q)-ary world, the sunflower condition is free. The real issue is growth.

The honest answer is:

1. A gap depending only on (k) is **false** in the full finite-state class.
2. If you fix the number of states, there is an explicit gap.
3. If you fix the sliding-window order (r), there is a much stronger, essentially optimal, explicit gap.

That gives the finite-state separation you asked for.

---

## 1. No memory-independent gap in the whole finite-state class

For each (r\ge 1), let (X^{(r)}) be the (q)-ary (r)-step shift forbidding only the block (0^r). Equivalently, in the (q)-ary de Bruijn graph (B_r(q)), delete the single edge (0^r).

This branch is irreducible and proper, hence not the full shift.

Let (a_n^{(r)}:=|L_n(X^{(r)})|). If you track the terminal run of zeros, you get
[
a_n^{(r)}=(q-1)\big(a_{n-1}^{(r)}+\cdots+a_{n-r}^{(r)}\big)\qquad (n\ge r),
]
with (a_n^{(r)}=q^n) for (0\le n<r). Hence its exponential growth rate is the Perron root (\lambda_{q,r}\in(q-1,q)) determined by
[
1=(q-1)\sum_{j=1}^r \lambda_{q,r}^{-j},
]
equivalently
[
\lambda_{q,r}^{r+1}-q\lambda_{q,r}^r+q-1=0,
\qquad
(q-\lambda_{q,r})\lambda_{q,r}^r=q-1.
]

Now fix any (\varepsilon>0). Since
[
(q-1)\sum_{j=1}^\infty (q-\varepsilon)^{-j}
=\frac{q-1}{q-\varepsilon-1}>1,
]
for all large (r) we have
[
(q-1)\sum_{j=1}^r (q-\varepsilon)^{-j}>1.
]
Because the left-hand side is strictly decreasing in (\lambda), this forces
[
\lambda_{q,r}>q-\varepsilon.
]
So
[
\lambda_{q,r}\uparrow q.
]

Therefore there is **no** (\eta_k>0) such that every irreducible proper (q)-ary finite-state branch satisfies
[
|L_n|\le (q-\eta_k)^n
]
in exponential rate, uniformly over all memories/state complexities.

So the global finite-state statement is false.

---

## 2. A general explicit gap if the number of states is fixed

This part uses the standard deterministic/right-resolving model for a finite-state branch.

### Theorem A

Let (X) be an irreducible right-resolving (q)-ary finite-state branch with (m) states, and let (L_n(X)) be its level-(n) language. Then exactly one of the following holds:

* (X) is the full (q)-shift, hence (|L_n(X)|=q^n) for all (n);
* or else, writing (n=tm+s) with (0\le s<m),
  [
  |L_n(X)|\le q^s,(q^m-1)^t.
  ]

In particular,
[
\limsup_{n\to\infty}|L_n(X)|^{1/n}\le \alpha_{q,m}:=(q^m-1)^{1/m}<q,
]
and
[
\alpha_{q,m}\le q-\frac1{m q^{m-1}}.
]

### Proof

If every state has all (q) labels leaving it, then from every state every (q)-ary word can be read, so the language is the full shift.

So assume (X) is not full. Then some state (t) is missing some letter (a). Since the graph is strongly connected, from every state (s) there is a directed path to (t) of length at most (m-1). Let (u_s) be one such label word, of length (\ell(s)\le m-1).

Then from state (s), every word beginning with (u_s a) is impossible. After padding to total length (m), at least one length-(m) word is missing from every state. Hence every state admits at most (q^m-1) words of length (m).

Now chop a length-(n) word into (t) blocks of length (m), plus a tail of length (s). The tail contributes at most (q^s), and each full (m)-block has at most (q^m-1) choices no matter which state you are in. So
[
|L_n(X)|\le q^s(q^m-1)^t.
]

Finally,
[
(q^m-1)^{1/m}
= q\bigl(1-q^{-m}\bigr)^{1/m}
\le q\left(1-\frac{q^{-m}}m\right)
= q-\frac1{m q^{m-1}}.
]
That proves Theorem A. (\square)

This already gives a genuine finite-state gap, but it depends on the state count (m), and it is far from sharp for high-memory branches.

---

## 3. The sharp fixed-order gap for (r)-step sliding-window branches

Now we pass to the stronger theorem you asked for.

An (r)-step (q)-ary branch means a sliding-window language determined by allowed (r)-blocks. Equivalently: a proper strongly connected subgraph of the (q)-ary de Bruijn graph (B_r(q)).

This is the right place to get an almost optimal theorem.

### Theorem B (optimal entropy gap for fixed order (r))

Let (X) be an irreducible (r)-step (q)-ary branch. Then exactly one of the following holds:

* (X) is the full (q)-shift, equivalently the full de Bruijn branch, and (|L_n(X)|=q^n) for all (n);
* or else
  [
  |L_n(X)|\le \frac{\lambda_{q,r}^{,n+1}}{q-1}\qquad (n\ge 0),
  ]
  where (\lambda_{q,r}\in(q-1,q)) is the unique root of
  [
  1=(q-1)\sum_{j=1}^r \lambda^{-j},
  ]
  equivalently
  [
  \lambda^{r+1}-q\lambda^r+q-1=0.
  ]

Hence
[
h(X):=\limsup_{n\to\infty}\frac1n\log |L_n(X)|
\le \log \lambda_{q,r},
]
and if (\delta_{q,r}:=q-\lambda_{q,r}), then
[
\delta_{q,r}=\frac{q-1}{\lambda_{q,r}^r}>\frac{q-1}{q^r}.
]
So in particular
[
h(X)\le \log!\left(q-\frac{q-1}{q^r}\right).
]

Moreover this is sharp in exponential rate: equality in entropy is attained by the irreducible branch forbidding only (0^r).

---

### Proof

Since (X) is a proper (r)-step branch, there exists a forbidden block
[
w=w_1\cdots w_r\in [q]^r.
]
Every word in (L_n(X)) avoids (w) as a contiguous factor. So it is enough to bound the number (A_w(n)) of length-(n) (q)-ary words avoiding (w).

#### The prefix automaton

Consider the standard prefix automaton for avoiding (w). Its states are (0,1,\dots,r-1), where state (j) means:

> the longest suffix of the word read so far that is also a prefix of (w) has length (j).

A letter that would complete an occurrence of (w) is forbidden.

Two key facts are immediate:

* if (j<r-1), then exactly one letter sends state (j) to state (j+1), namely (w_{j+1});
* every other allowed letter from state (j) sends you to some state (\le j);
* from state (r-1), the single letter (w_r) is forbidden, and all other (q-1) letters send you to states (\le r-1).

Let (M_w) be the transition matrix of this automaton.

#### The comparison vector

Let (\lambda=\lambda_{q,r}) be defined by
[
1=(q-1)\sum_{m=1}^r \lambda^{-m}.
]
Define a positive vector (v=(v_0,\dots,v_{r-1})^T) by
[
v_j:=(q-1)\sum_{m=1}^{r-j}\lambda^{-m}.
]
Then
[
v_0=1,\qquad v_{r-1}=\frac{q-1}{\lambda},
]
and (v_0>v_1>\cdots>v_{r-1}>0).

Also,
[
\lambda v_j=(q-1)v_0+v_{j+1}\qquad (0\le j\le r-2),
]
and
[
\lambda v_{r-1}=(q-1)v_0.
]

Now compare one row at a time.

If (j<r-1), then one allowed letter goes to (j+1), while the other (q-1) allowed letters go to states (\le j), where (v) is at most (v_0). Therefore
[
(M_w v)*j\le v*{j+1}+(q-1)v_0=\lambda v_j.
]

If (j=r-1), all (q-1) allowed letters go to states of weight at most (v_0), so
[
(M_w v)*{r-1}\le (q-1)v_0=\lambda v*{r-1}.
]

Hence
[
M_w v\le \lambda v.
]

By induction,
[
M_w^n v\le \lambda^n v.
]

#### Counting avoiders

Starting from state (0), the number of length-(n) words avoiding (w) is
[
A_w(n)=e_0^T M_w^n \mathbf 1.
]
Since every coordinate of (\mathbf 1) is at most (v/v_{r-1}),
[
\mathbf 1\le \frac1{v_{r-1}},v.
]
Therefore
[
A_w(n)
\le \frac1{v_{r-1}}, e_0^T M_w^n v
\le \frac1{v_{r-1}}, \lambda^n e_0^T v
= \frac{v_0}{v_{r-1}},\lambda^n
= \frac{\lambda^{n+1}}{q-1}.
]

Since (L_n(X)\subseteq{\text{words avoiding }w}), we get
[
|L_n(X)|\le A_w(n)\le \frac{\lambda_{q,r}^{,n+1}}{q-1}.
]
This proves the bound.

Finally, for the branch forbidding only (0^r), the same automaton is exactly the run-length automaton for consecutive zeros, and all the above inequalities become equalities in the Perron calculation. So that branch has entropy exactly (\log \lambda_{q,r}). It is irreducible, hence the bound is sharp. (\square)

---

## 4. What this says in the (k)-sunflower language

Recall (q=k-1).

So, inside the finite-state (q)-ary model:

* the only exact growth-(q) survivor is the full (q)-shift / full de Bruijn branch;
* no gap (\eta_k>0) independent of memory can hold in the whole class;
* but for (r)-step branches one has the explicit sharp entropy gap
  [
  \limsup_{n\to\infty}|L_n|^{1/n}\le \lambda_{k-1,r},
  ]
  where (\lambda_{k-1,r}) is the unique root in ((k-2,k-1)) of
  [
  \lambda^{r+1}-(k-1)\lambda^r+k-2=0.
  ]
  Equivalently,
  [
  \lambda_{k-1,r}= (k-1)-\delta_{k,r},
  \qquad
  \delta_{k,r}>\frac{k-2}{(k-1)^r}.
  ]

So the strongest honest theorem is:

* **global (k)-only gap:** false;
* **fixed state count (m):** explicit gap (q-(q^m-1)^{1/m});
* **fixed order (r):** optimal explicit gap given by (\lambda_{q,r}), attained by forbidding a single block (0^r).

If you want, I can push this one step further and rewrite Theorem B purely as a statement about proper strongly connected subgraphs of the de Bruijn graph (B_r(q)) and their Perron roots.
