# Probabilistic programming using delimited continuations

This directory contains some work I did comparing a few different ways
of implementing probabilistic programming based on Oleg Kiselyov's
Hansei system, which is in turn based on his `delimcc` package providing
delimited continuations (shift and reset) in OCaml.

The result is that you can represent monadic effects in so called 'direct'
form, ie, without lifting everything into the monad, using normal code
for the pure parts of the computation, and invoking the monadic effects
only when they are needed.

The timings directory contains some timing results.

Now that delimcc is a package installed by opam, some things in the Makefile
don't work so I need to refresh it to get everything working again.
