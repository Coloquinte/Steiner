/*
 * coloquinte_flute.cxx
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

#include <vector>
#include <array>
#include <bitset>
#include <functional>
#include <algorithm>
#include <cmath>
#include <cassert>

#include <iostream>

const int hard_max_table_lookup = 9;
const int hard_max_tree_lookup = 12;

template<typename T>
struct point{
    T x, y;
    point(T a, T b) : x(a), y(b){}
};

template<typename T>
struct labeled_point : public point<T>{
    int ind;
    labeled_point(T a, T b, int i) : point(a, b), ind(i){}
};



template<int n>
struct lookup_struct{
    // First the x entries (n-3 positive from 2 to n-1 then n-3 negative from 1 to n-2), then the y entries
    // On a Steiner trees, the first and last entries are not taken into account (always negative/always positive)
    // The second may not be positive, like the n-2 one cannot be negative, hence the n-3 entries
    std::bitset<4*n - 12> cost;

    // Could be vectorized quite easily on AVX
    template<typename T>
    T evaluate(std::array<T, 4*n-12> position_vector){
        std::array<T, 4*n-12> masked;
        for(int i=0; i < 4*n -12; ++i){
            masked[i] = (cost[i] ? position_vector[i] : 0);
        }
        return std::accumulate(masked.begin(), masked.end(), 0);
    }

    lookup_struct(){
        for(int i=0; i<4*n-12; ++i){
            cost[b] = false;
        }
    }

    // All of them assume everything is initialized to false
    void set_positive_x(int ind){
        assert(ind > 1);
        assert(ind < n-1);
        cost[ind - 2] = true;
    }
    void set_negative_x(int ind){
        assert(ind > 0);
        assert(ind < n-2);
        cost[n-3+ind-1] = true;
    }
    void set_positive_y(int ind){
        assert(ind > 1);
        assert(ind < n-1);
        cost[2*n-6+ind-2] = true;
    }
    void set_negative_y(int ind){
        assert(ind > 0);
        assert(ind < n-2);
        cost[3*n-9+ind-1] = true;
    }
};

// Dominates another POWV (non strict)
template<int n>
bool dominates(lookup_struct<n> const & a, lookup_struct<n> const & b) const{
    // Avoid code duplication between x and y
    auto evaluate = [&](int inpos)->bool{
        const int neg_offset = n-3;
        bool ret = true;
        // Cost of b on this edge - cost of a on this edge
        int active = 0;
        if(a.cost[inpos]){
            --active;
        }
        if(b.cost[inpos]){
            ++active;
        }
        ret = ret && active >= 0;
        for(int i=0; i<n-4; ++i){
            if(b.cost[inpos+i+1]){
                ++active;
            }
            if(a.cost[inpos+i+1]){
                --active;
            }
            if(b.cost[inpos+neg_offset+i]){
                --active;
            }
            if(a.cost[inpos+neg_offset+i]){
                ++active;
            }
            ret = ret && active >= 0;
        }
        if(b.cost[inpos+neg_offset+i]){
            --active;
        }
        if(a.cost[inpos+neg_offset+i]){
            ++active;
        }
        ret = ret && active >= 0;

        return ret;
    };
    return evaluate(0) and evaluate(2*n-6);
}

// Both arrays are in order
template<typename T, int n>
std::array<T, 4*n - 12> get_lookup_array(std::array<T, n> x_pos, std::array<T, n> y_pos){
    std::array<T, 4*n - 12> ret;
    for(int i=0; i<n-3; ++i){
        ret[       i] =  x_pos[i+1];
        ret[n-3   +i] = -x_pos[i+2];
    }
    for(int i=0; i<n-3; ++i){
        ret[2*n-6 +i] =  y_pos[i+1];
        ret[3*n-9 +i] = -y_pos[i+2];
    }
    return ret;
}

template<int n>
struct sorted_tree{
    static_assert(n >= 2, "A tree must have at least 2 vertices");

    std::array<unsigned char, 2*n-2> edges;

    // To prune obviously suboptimal Steiner trees and keep only one representant for equivalent ones if agressive is set to true
    bool is_kept(bool agressive = true) const{
        std::array<int, n> before, after;
        for(int i=0; i<n; ++i){ before[i] = 0; after[i] = 0; }

        for(int i=0; i<n-1; ++i){
            unsigned char f = edges[2*i], s = edges[2*i+1];
            assert(f != s);
            if(f < s){
                after[f]++; before[s]++;
            }
            else{
                after[s]++; before[f]++;
            }
        }
        bool feasible = true;
        for(int i=0; i<n; ++i){
            feasible = feasible and std::abs(after[i] - before[i]) <= 1 and (!agressive or before[i] <= after[i] or after[i] == 0); // If agressive, keep only one representant where the vertical edge is at the leftmost possible position
        }
        return feasible;
    }

    // Assumes the tree is at least potentially optimal
    lookup_struct<n> get_lookup_cost(std::array<int, n> permutation) const{
        lookup_struct<n> ret;
        for(bool & b : ret.cost){ b=false; }

        std::array<int, n> min_branch, max_branch;
        for(int i=0; i<n; ++i){
            min_branch[i] = permutation[i];
            max_branch[i] = permutation[i];
        }
        
        std::array<int, n> before, after;
        for(int i=0; i<n; ++i){ before[i] = 0; after[i] = 0; }

        for(int j=0; j<2*n-2; j+=2){
            // y cost
            // The edge is the current pair of uint8_t
            f = edges[j]; s = edges[j+1];
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);

            // Set the cost in the lookup table
            if(min_branch[f] != 0 and min_branch[f] != n-1){
                ret.set_negative_y(min_branch[f]);
            }
            if(max_branch[f] != 0 and max_branch[f] != n-1){
                ret.set_positive_y(min_branch[f]);
            }


            // x cost
            unsigned char f = edges[j], s = edges[j+1+1];
            if(f < s){
                after[f]++; before[s]++;
            }
            else{
                after[s]++; before[f]++;
            }
        }

        // Final calculation of the x cost
        for(int i=1; i<n-1; ++i){
            if(after[i] < before[i]){
                ret.set_positive_x(i);
            }
            if(after[i] > before[i]){
                ret.set_negative_x(i);
            }
        }
        return ret;
    }

    // The x array is in sorted order, the y array in the corresponding order
    template<typename T>
    T get_cost(std::array<T, n> x_pos, std::array<T, n> y_pos) const{
        T cost = 0;
        std::array<T, n> min_branch, max_branch;
        for(int i=0; i<n; ++i){
            min_branch[i] = y_pos[i];
            max_branch[i] = y_pos[i];
        }
        int f,s;
        for(int j=0; j<2*n-2; j+=2){
            // The edge is the current pair of uint8_t
            f = edges[j]; s = edges[j+1];
            cost += (x_pos[s] - x_pos[f]);
            cost += (max_branch[f] - min_branch[f]);
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);
        }
        cost += (max_branch[s] - min_branch[s]);
        return cost;
    }
};

// Various comparison functions; they change the outcome when selecting trees for cover
bool basic_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    return a.edges < b.edges;
}
bool first_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = a.edges[2*i];
        b_e[i] = b.edges[2*i];
    }
    return a_e < b_e;
}
bool prufer_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = a.edges[2*i+1];
        b_e[i] = b.edges[2*i+1];
    }
    return a_e < b_e;
}
bool smallest_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = std::min(a.edges[2*i], a.edges[2*i+1]);
        b_e[i] = std::min(b.edges[2*i], b.edges[2*i+1]);
    }
    return a_e < b_e;
}


bool operator<(sorted_tree<n> const a, sorted_tree<n> const b){
    return smallest_lexicographic(a, b);
}

// Greedy minimum set cover algorithm to get the best subset of the trees
std::vector<int> min_cover(std::vector<std::vector<int> > const & set_coverers, int nb_coverers){
    std::vector<std::vector<int> > current_sets = set_coverers;
    std::vector<int> current_to_origin(nb_coverers);
    std::vector<int> current_cover;

    for(int i=0; i < current_to_origin.size(); ++i){
        current_to_origin[i] = i;
    }

    while(current_sets.size() != 0){
        // Find the biggest cover with one element
        std::vector<int> nb_covered(current_to_origin.size(), 0);
        for(auto const & V : current_sets){
            for(int s : V){
                nb_covered[s]++;
            }
        }

        std::vector<int> new_current_to_origin;
        std::vector<int> old_to_new(current_to_origin.size(), -1);

        int max_cover = 0, max_index = -1;
        for(int i=0; i<nb_covered.size(); ++i){
            if(nb_covered[i] > 0){
                // Keep the ones that still cover something
                old_to_new[i] = new_current_to_origin.size();
                new_current_to_origin.push_back(current_to_origin[i]);
                if(nb_covered[i] > max_cover){
                    max_cover = nb_covered[i];
                    max_index = i;
                }
            }
        }

        current_cover.push_back(current_to_origin[max_index]);

        // Keep the sets that are still not covered
        std::vector<std::vector<int> > new_sets;
        for(auto const & V : current_sets){
            bool covered = false;
            std::vector<int> new_indices;
            for(int s : V){
                covered = covered or (s == max_index);
                new_indices.push_back(old_to_new[s]);
            }
            if(!covered){
                new_sets.push_back(new_indices);
            }
        }
        current_sets = new_sets;
        current_to_origin = new_current_to_origin;
    }
    return current_cover;
}

template<int n>
sorted_tree<n> decode_prufer(std::array<unsigned char, n-2> const prufer_representation){
    sorted_tree<n> ret;

    std::array<int, n> degrees(n, 1), degrees;
    for(int & d : degrees){ d = 1; }
    for(unsigned char const p : prufer_representation){
        degrees[p]++;
    }

    for(int k=0; k<n-2; k++){
        unsigned char p = prufer_representation[k];
        int i=0;
        while(degrees[i] != 1){
            assert(i < n);
            ++i;
        }
        ret.edges[2*k] = i; ret.edges[2*k+1] = p;
        degrees[i]--;
        degrees[p]--;
    }
    int i=0;
    while(degrees[i] != 1){
        ++i;
        assert(i<n-1);
    }
    int j=i+1;
    while(degrees[j] != 1){
        ++j;
        assert(j<n);
    }
    ret.edges[2*n-4] = i; ret.edges[2*n-3] = j;
    return ret;
}

template<int n>
std::vector<sorted_tree<n> > generate_trees(bool agressive=true){
    std::vector<sorted_tree<n> > ret;
    std::array<int, n-2> A;
    auto rec_helper = [&](int size){
        if(size > 0){
            for(int i=1; i<n-1; ++i){ // We do not need to generate trees with degree more than 1 for nodes 0 and n-1: this efficiently restricts the bruteforce
                A[size-1] = i;
                rec_helper(A, size-1, ret);
            }
        }
        else{
            sorted_tree<n> tr = decode_prufer(A);
            if(tr.is_kept(agressive)){
                ret.push_back(tr);
            }
        }
    };

    rec_helper(n-2);

    return ret_val;
}

template<int n>
std::vector<std::array<unsigned char, n> > get_permutations(){
    std::vector<std::array<unsigned char, n> > ret;
    static_assert(n >= 2, "Too small");
    std::array<unsigned char, n> sigma;
    for(int i=0; i<n; ++i){
        sigma[i] = i;
    }
    do{
        ret.push_back(sigma);
    }while(std::next_permutation(sigma.begin(), sigma.end()));
    return ret;
}

// Get the POWVs for the permutation and the corresponding trees
template<int n>
std::vector<std::pair<lookup_struct<n>, std::vector<int> > > get_cover(std::vector<sorted_tree<n> > const & trees, std::array<int, n> sigma){
    std::unordered_map<lookup_struct<n>, std::vector<int> > costs;
    for(int i=0; i<trees.size(); ++i){
        lookup_struct<n> cur_cost = trees[i].get_lookup_cost(sigma);

        // Insert in the multimap and remove dominated costs
        auto cur_it = costs.find(cur_cost);
        if(cur_it != costs.end()){ // Already in the map: add an entry
            cur_it->second.push_back(i);
        }
        else{ // Not in the map: should we insert it/remove other entries
            bool to_insert = true;
            for(auto it = costs.begin(); it != costs.end(); ++it){
                lookup_struct<n> const old_cost = it->first;
                // old_cost != cur_cost since cur_cost is not in the multimap
                if(old_cost.dominates(cur_cost)){
                    to_insert = false;
                }
                else if(cur_cost.dominates(old_cost)){
                    costs.erase(it);// remove old_cost
                }
            }
            if(to_insert){
                std::pair<lookup_struct<n>, std::vector<int> > elt(cur_cost, std::vector<int>(1, i));
                costs.insert(elt);
            }
        }
    }
    // Push the remaining indices to the vector
    std::vector<std::pair<lookup_struct<n>, std::vector<int> > > sigmas_cover;
    for(auto it = costs.begin(); it != costs.end(); ++it){
        sigmas_cover.push_back(*it);
    }
    return sigmas_cover; 
}

// Just get a set of trees that cover every POWV of every permutation: the goal is to generate a tree lookup table
template<int n>
std::vector<std::vector<std::pair<lookup_struct<n>, std::vector<int> > > > get_cover(std::vector<sorted_tree<n> > const & trees, std::vector<std::array<int, n> > const & permutations){
    std::vector<std::vector<int> > set_coverers;

    for(auto sigma : permutations){
        set_coverers.push_back(get_cover<n>(trees, sigma));
    }
    return set_coverers;
}


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

