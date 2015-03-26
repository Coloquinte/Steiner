# Steiner tree lookup table

This code was used to generate the lookup tables used by Coloquinte's Steiner tree calculation.
It reduces the number of possible topologies, which makes the lookup table smaller than Flute's at the cost of more (but vectorizable) calculations for each tree.

I should probably introduce this method in Flute to reduce the size of its lookup table or write a paper about my method, but I just don't hav enough time.
