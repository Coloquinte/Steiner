/*
 * coloquinte_calc.hxx
 *
 * Copyright 2013 Gabriel Gouvine <gabriel.gouvine@polytechnique.edu>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301, USA.
 *
 *
 */

#include "coloquinte_flute.hxx"

const int hard_max_table_lookup = 9;
const int hard_max_tree_lookup = 12;

class flute{
    // static_assert(n >= 4, "The wirelength is optimal up to 4 pins without a lookup table: don't instantiate the class with less than 4 pins");

    int table_max_lookup; // Max pin count for the flute-like lookup table
    int tree_max_lookup;  // Max pin count for x-connextivity based lookup table
    int min_lookup;       // First lookup number in the vectors; usually 4 or 5 pins, since 3 is easy to solve

    /*
     * The lookup table: a mask of booleans for the wirelength vectors and an index in the tree array for the corresponding trees
     */
    std::vector<std::vector<uint32_t> > POWVs; // Potentially optimal wirelength vectors for each number of pins
    std::vector<std::vector<uint16_t> > POSTs; // Indices of the connexions for the potentially optimal Steiner tree
    std::vector<int> end_index;                // End of the lookup records for a given index

    /*
     * The trees corresponding to the optimal connexions; their size is negligible compared to the lookup table
     * There are 642 of them for 8 pins, 4334 for 9 and 33510 for 10 if pruned
     * When pruned from the lookup table, there are only 210 for 8 pins, 1122 for 9 pins
     *
     * Note that we could bruteforce from them rather than the table, thus lowering the cache thrashing by two orders of magnitude (16kio instead of 3000 for the 9 pins table) at the cost of an increased CPU time; we could use one byte/edge but it could cost too much CPU time
     */

    std::vector<std::vector<uint8_t> > trees; // For each number of pins, enumerate all the trees in order, one edge pair at a time


    // Performs a lookup; return the corresponding index of the optimal POWV/POST and the associated length as a reference parameter
    template<int n, typename T>
    int perform_table_lookup(int lookup_index, std::array<T, n> x_pos, std::array<T, n> y_pos, T & minimum_length) const{
        std::array<T, 4*n-8> lookup_array = get_lookup_array<T, n>(x_pos, y_pos);

        std::vector<T> wirelength(end_index[lookup_index+1] - end_index[lookup_index]);
        for(int i=end_index[lookup_index], j=0; i<end_index[lookup_index+1]; ++i, ++j){
            lookup_struct<n> current_POWV(POWVs[i]);
            wirelength[j] = current_POWV.evaluate(lookup_array);
        }
        auto min_elt = std::min_element(wirelength.begin(), wirelength.end());
        minimum_length = *min_elt;
        return min_elt - wirelength.begin() + end_index[lookup_index];
    }

    template<int n, typename T>
    T perform_tree_lookup(std::array<T, n> x_pos, std::array<T, n> y_pos) const{
        assert(n >= min_lookup);
        T min_cost = std::numeric_limits<T>::max();
        int min_index = 0;

        for(int i=0; i<trees[n-min_lookup].size(); i += (2*n-2)){
            sorted_tree<n> tr;
            for(int j=0; j<2*n-2; j+=2){
                tr.edges[j]   = trees[i+j];
                tr.edges[j+1] = trees[i+j+1];
            }
            T cost = tr.get_cost(x_pos, y_pos);
            if(cost < min_cost){
                min_cost = cost;
                min_index = i;
            }
        }
        return min_cost; 
    }

    // From a set of pins return the minimal wirelength and the set of x connexions, y connexions
    template<int n, typename T>
    void full_table_lookup(std::array<labeled_point<T>, n> positions, T & minimum_length, std::array<int, 2*n-2> & x_tree, std::array<int, 2*n-2> y_tree) const{
        // Sort on x while keeping the original indices to get a tree if needed
        std::sort(positions.begin(), positions.end(), [](labeled_point<T> const a, labeled_point<T> const b)->bool{ return a.x < b.x; });
        std::array<int, n> x_to_orig(positions.size()); // From the sorted order to the original one
        std::array<T, n> x_pos(positions.size()), y_pos(positions.size()); // The positions in the sorted order (by x)
        for(int i=0; i<n; ++i){
            x_to_orig[i] = labeled_pos[i].ind;
            labeled_pos[i].ind = i;
            x_pos[i] = labeled_pos[i].x;
            y_pos[i] = labeled_pos[i].y;
        }

        std::sort(positions.begin(), positions.end(), [](labeled_point<T> const a, labeled_point<T> const b)->bool{ return a.y < b.y; });
        std::array<int, n> x_to_y(positions.size());
        for(int i=0; i<n; ++i){
            x_to_y[labeled_pos[i].ind] = i;
        }

        // Get the lookup index and modify the vectors accordingly

        perform_table_lookup(lookup_index, x_pos, y_pos, minimum_length);
    }

    // TODO
    template<typename T, int n>
    void get_table_index_and_permutations(){

    }

    public:

    void dumb_initialize(int max_table_lookup, int max_tree_lookup=-1){
        max_tree_lookup = std::max(max_table_lookup, max_tree_lookup);
        // TODO
    }

    template<typename T>
    T get_wirelength(std::vector<point<T> > positions) const{
        if(max_lookup >= positions.size()){
            if(positions.size() <= 3){ // For less than 3 pins, it is just the half-perimeter wirelength
                T xmin = std::min(positions.begin(), positions.end(), [](point<T> const a, point<T> const b)->bool{ return a.x < b.x; }).x;
                T xmax = std::max(positions.begin(), positions.end(), [](point<T> const a, point<T> const b)->bool{ return a.x < b.x; }).x;
                T ymin = std::min(positions.begin(), positions.end(), [](point<T> const a, point<T> const b)->bool{ return a.y < b.y; }).y;
                T ymax = std::max(positions.begin(), positions.end(), [](point<T> const a, point<T> const b)->bool{ return a.y < b.y; }).y;
                return (xmax - xmin) + (ymax - ymin);
            }
            // Should be able to have some direct code for 4 pins
            
            /*
             *  Code for the table lookup
             */

        }
        else{ // Either presort and cut on x/y or create a spanning tree to cut

        }
    }

    template<typename T>
    std::pair<tree, tree> get_connexions() const{
        
    }
};

