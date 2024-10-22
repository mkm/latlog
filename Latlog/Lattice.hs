module Latlog.Lattice (
        Lattice(..),
        BoundedLattice(..),
    ) where

infixl 2 \/
infixl 3 /\

class Lattice a where
    (/\) :: a -> a -> a
    (\/) :: a -> a -> a
    neg :: a -> a

    x /\ y = neg (neg x \/ neg y)
    x \/ y = neg (neg x /\ neg y)

class Lattice a => BoundedLattice a where
    top :: a
    bottom :: a

    top = neg bottom
    bottom = neg top

instance Lattice Bool where
    (/\) = (&&)
    (\/) = (||)
    neg = not

instance Lattice b => Lattice (a -> b) where
    f /\ g = \x -> f x /\ g x
    f \/ g = \x -> f x \/ g x
    neg f = \x -> neg (f x)

