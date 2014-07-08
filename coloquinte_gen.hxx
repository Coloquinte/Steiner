/*
 * coloquinte_gen.hxx
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
#include <iostream>

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
std::vector<std::array<unsigned char, n> > generate_permutations(){
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

