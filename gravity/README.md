# Gravitational motion simulator

This program simulates the motion of massive objects under gravitational interaction --
stars, planets and moons if you like.

This code was written around December 2016 but I'm only just putting it in a github repo.

The ideas behind this implementation are:

- Express the dynamics in terms of a Hamiltonian, ie an energy function that includes
  the gravitation potential energies and the kinetic energies.

- Derive the equations of motion by differentiation of the Hamiltonian

- Do the differentation *symbolically* - ie, the Hamiltonian is expressed as a symbolic
  formula and the equations of motion are symbolic equations which only have to be derived
  once. After that, we just evaluate the symbolic expression with numerical substitions
  for the variables.

- Parameterise Hamiltonian computation by a module representing the vector space in which
  the computations are done. These can be normal numerical vectors (ie lists of numbers),
  or symbolic vectors (lists of symbolic expressions).

- Integrate the equations of motion using a 4th order Runge-Kutta integrator. This is an
  ok integrator, but it does not conserve energy, so the system can run away. What we need
  is a *symplectic* integrator that conserves energy, but I haven't got round to doing that.

## Prequisites

You need an OCaml with a working lablgtk package installed. Hence you might also need
an X11 server unless you have a Gtk built for Mac OS using the native graphics system.

## Building

Type `make` and pray.

## Running

The `gravity` command takes an integer to select one of the predefined systems and two
floating point numbers representing the time step for integration and a small number
which removes the singularity at the bottom of the gravitational potential well - that is
instead of diverging towards minus infinity as the distance goes to zero, the potential
transitions to a quadratic energy well. For example
```
./gravity 0 0.002 0.0001
```
will run a system with one sun and two planets. I get some hundreds of frames per second
on a 2012 MacBook Pro running under XQuartz. You can press 'q' to exit. There are other
keyboard commands.

The available systems are:

    0: 1 star, 2 planets
    1: 1 star, 3 planets, one of which orbits in the other direction
    2: 1 star, 1 planet, 1 moon orbiting, and 1 spacecraft initially orbiting the moon
    3: Binary star system with 2 stars in a tight orbit, with 2 planets

The keyboard commands are

    'q' -> quit
    '<' -> half integration time step
    '>' -> double integration time step
    '[' -> slow down simulation
    ']' -> speed up simulation
    'r' -> reverse time
    '-' -> zoom out
    '=' -> zoom in
    'i' -> return to initial positions and velocities
    '0' -> centre view on origin (initial view)
    '1' -> centre view on first object
    '2' -> centre view on second object
    '3' -> centre view on third object
    '4' -> centre view on fourth object

## Running from OCaml command line

You might be able to get this working from an interactive top level, eg `ocaml`
or `utop`. I've included my `.ocamlinit` file to give you a hint as to how to
set it up, but you will have to edit it.
