# Probabilistic programming using delimited continuations

This directory contains some work I did comparing a few different ways
of implementing probabilistic programming based on the ideas in Oleg Kiselyov's
Hansei system, which is in turn based on his `delimcc` package providing
delimited continuations (shift and reset) in OCaml.

The result is that you can represent monadic effects in so called 'direct'
form, ie, without lifting everything into the monad, using normal code
for the pure parts of the computation, and invoking the monadic effects
only when they are needed.

The timings directory contains some timing results.

Now that delimcc is a package installed by opam, some of the build steps
in the Makefile aren't working and needs a bit of a refresh.

The included history files contain records of some of my command line
interactions, so when everything is working again, they will be a usefull
reminder of how this works in practise.

NB. The code under okmij is NOT mine - it was written by Oleg Kiselyov.
See https://okmij.org/ftp/kakuritu/Hansei.html 
