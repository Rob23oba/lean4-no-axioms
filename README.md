# Lean 4 without any axioms

This repository is an experiment to see how much you can do without any of Lean's standard axioms, that is:
- without propositional extensionality (`propext`)
- without useful quotients (`Quot.sound`)
- without functional extensionality (`funext`, consequence of `Quot.sound`)
- without choice (`Classical.choice`)
- without law of excluded middle (consequence of all three axioms)

The end goal of this is (for now) to formalize ZF (without choice) (mostly done) and real number arithmetic.
