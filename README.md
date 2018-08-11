# ComparisonTheorem-MacLane

Mac Lane's Comparison Theorem for the (co)Kleisli Construction in Coq.

- `make` to compile with `coqc 8.8.1`, `8.8.0` or `8.7.2`.
-------------
## Sources   
* Category.v: Implements the category class, includes some example categories. I.e., Coq's prop as a category of propositional formulas and entailements
* Functor.v : Implements the functor class, includes sameness of functors lemma using JMeq and some example functors. I.e., conjunction and implication as functor instances, the 2-category
* NaturalTransformation.v: Implements the natural transformation class, includes sameness of functors lemma using JMeq and some examples. I.e., the functor category
* Monad.v: Implements the (co)monad class, includes the (co)Kleisli category of a (co)monad
* Adjunction.v: Implements the adjunction class, includes the formal proofs of `a (co)monad gives a (co)Kleisli adjunction` and `an adjunction gives a monad`
* Comparison.v: Includes the `comparison functor L` and the proof of the `comparison theorem for the Kleisli construction`
* UseCase.v: Includes the use case of the comparison theorem where a Kleisli adjunction followed by coKleils adjunction annihilate each other through the comparison functor.
