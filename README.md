# Steiner tree lookup table

This code was used to generate the lookup tables used by Coloquinte's Steiner tree calculation.
It reduces the number of possible topologies, which makes the lookup table smaller than Flute's at the cost of more (but vectorizable) calculations for each tree.

The method is described in the report in the coloquinte source tree. Performance-wise, I wasn't able to do as well as Flute ^^
