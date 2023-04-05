Let's understand the Simply-typed lambda calculus (STLC) through formalization in Agda.

We prove standard type soundness results (progress and preservation), 
decidability of typechecking,
and strong normalization.

See `small.pdf` for a dependency graph.

Although the STLC seems very simple, proving its main theorems is an excellent way to understand the techniques
used to prove properties of more complicated languages.

The first hurdle that any programming language formalization must deal with is how to represent and work with variable binding.
Here, we use de Brujin indices with _intrinsically scoped terms_.
De Brujin indices are a simple, "low-tech" method of representing variables that circumvents the issue of dealing with alpha-equivalent terms.
Using intrinsically scoped terms prevents us from writing variable indices that do not refer to anything.
Unlike some other presentations of the STLC, however, we do not use _intrinsically typed terms_, which would prevent any ill-typed terms from being written at all.
While convenient, our opinion is that this is less educational as it does not scale as well to more complex type systems.

We show that the STLC is _sound_, meaning that a well-typed program cannot "go wrong" or "get stuck".
Again, the main technical challenges here deal with variable binding.
In particular, in order to prove that reduction preserves typing, we must explain how substitution interacts with typing,
which requires proving a standard "substitution lemma".
We use the framework of parallel substitutions to define our substitutions.

Typechecking in STLC is decidable.
We demonstrate this by writing a typechecking algorithm that is sound and complete.

STLC also enjoys a strong property known as _normalization_, meaning that every
well-typed program will reduce to a value in a finite number of reduction steps.
We present a standard proof based on logical relations, adapted from the book Types and Programming Languages.
